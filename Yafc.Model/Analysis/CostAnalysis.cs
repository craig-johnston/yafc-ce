using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using Google.OrTools.LinearSolver;
using Serilog;
using Yafc.I18n;
using Yafc.UI;

namespace Yafc.Model;

public class CostAnalysis(bool onlyCurrentMilestones) : Analysis {
    private readonly ILogger logger = Logging.GetLogger<CostAnalysis>();

    public static readonly CostAnalysis Instance = new CostAnalysis(false);
    public static readonly CostAnalysis InstanceAtMilestones = new CostAnalysis(true);
    public static CostAnalysis Get(bool atCurrentMilestones) => atCurrentMilestones ? InstanceAtMilestones : Instance;

    private const float CostPerSecond = 0.1f;
    private const float CostPerMj = 0.1f;
    private const float CostPerIngredientPerSize = 0.1f;
    private const float CostPerProductPerSize = 0.2f;
    private const float CostPerItem = 0.02f;
    private const float CostPerFluid = 0.0005f;
    private const float CostPerPollution = 0.01f;
    private const float CostLowerLimit = -10f;
    private const float CostLimitWhenGeneratesOnMap = 1e4f;
    private const float MiningPenalty = 1f; // Penalty for any mining
    private const float MiningMaxDensityForPenalty = 2000; // Mining things with less density than this gets extra penalty
    private const float MiningMaxExtraPenaltyForRarity = 10f;

    public Mapping<FactorioObject, float> cost;
    public Mapping<Recipe, float> recipeCost;
    public Mapping<RecipeOrTechnology, float> recipeProductCost;
    public Mapping<FactorioObject, float> flow;
    public Mapping<Recipe, float> recipeWastePercentage;
    public Goods[]? importantItems;
    private readonly bool onlyCurrentMilestones = onlyCurrentMilestones;
    private string? itemAmountPrefix;

    private bool ShouldInclude(FactorioObject obj) => onlyCurrentMilestones ? obj.IsAutomatableWithCurrentMilestones() : obj.IsAutomatable();

    public override void Compute(Project project, ErrorCollector warnings) {
        var workspaceSolver = DataUtils.CreateSolver();
        var objective = workspaceSolver.Objective();
        objective.SetMaximization();
        Stopwatch time = Stopwatch.StartNew();

        // Find the best accessible container for spoilage cost calculation
        float bestContainerSlotsPerTile = 1f;
        foreach (var container in Database.allContainers) {
            float area = container.width * container.height;
            if (ShouldInclude(container) && area > 0) {
                float slotsPerTile = container.inventorySize / area;
                if (slotsPerTile > bestContainerSlotsPerTile) {
                    bestContainerSlotsPerTile = slotsPerTile;
                }
            }
        }

        var variables = Database.goods.CreateMapping<Variable>();
        var constraints = Database.recipes.CreateMapping<Constraint>();

        Dictionary<Goods, float> sciencePackUsage = [];
        if (!onlyCurrentMilestones && project.preferences.targetTechnology != null) {
            itemAmountPrefix = LSs.CostAnalysisEstimatedAmountFor.L(project.preferences.targetTechnology.locName);

            foreach (var spUsage in TechnologyScienceAnalysis.Instance.allSciencePacks[project.preferences.targetTechnology]) {
                sciencePackUsage[spUsage.goods] = spUsage.amount;
            }
        }
        else {
            itemAmountPrefix = LSs.CostAnalysisEstimatedAmount;

            foreach (Technology technology in Database.technologies.all.ExceptExcluded(this)) {
                if (technology.IsAccessible() && technology.ingredients is not null) {
                    foreach (var ingredient in technology.ingredients) {
                        if (ingredient.goods.IsAutomatable()) {
                            if (onlyCurrentMilestones && !Milestones.Instance.IsAccessibleAtNextMilestone(ingredient.goods)) {
                                continue;
                            }

                            _ = sciencePackUsage.TryGetValue(ingredient.goods, out float prev);
                            sciencePackUsage[ingredient.goods] = prev + (ingredient.amount * technology.count);
                        }
                    }
                }
            }
        }

        foreach (Goods goods in Database.goods.all.ExceptExcluded(this)) {
            if (!ShouldInclude(goods)) {
                continue;
            }

            float mapGeneratedAmount = 0f;

            foreach (var src in goods.miscSources) {
                if (src is Entity ent && ent.mapGenerated) {
                    foreach (var product in ent.loot) {
                        if (product.goods == goods) {
                            mapGeneratedAmount += product.amount;
                        }
                    }
                }
            }

            var variable = workspaceSolver.MakeVar(CostLowerLimit, CostLimitWhenGeneratesOnMap / mapGeneratedAmount, false, goods.name);
            objective.SetCoefficient(variable, 1e-3); // adding small amount to each object cost, so even objects that aren't required for science will get cost calculated
            variables[goods] = variable;
        }

        foreach (var (item, count) in sciencePackUsage) {
            objective.SetCoefficient(variables[item], count / 1000f);
        }

        var export = Database.objects.CreateMapping<float>();
        var recipeProductionCost = Database.recipesAndTechnologies.CreateMapping<float>();
        recipeCost = Database.recipes.CreateMapping<float>();
        flow = Database.objects.CreateMapping<float>();
        var lastVariable = Database.goods.CreateMapping<Variable>();

        foreach (Recipe recipe in Database.recipes.all.ExceptExcluded(this)) {
            if (!ShouldInclude(recipe)) {
                continue;
            }

            if (onlyCurrentMilestones && !recipe.IsAccessibleWithCurrentMilestones()) {
                continue;
            }

            bool isFuelGroupConversion = recipe is Mechanics && recipe.name.StartsWith("fuel-group-recipe.", StringComparison.Ordinal);

            static bool ExcludeFuelFromCost(Goods fuel)
                => fuel is Fluid fluid && fluid.originalName == "steam"
                    || fuel is Special special && (special.name == "heat" || special.name.StartsWith("heat@", StringComparison.Ordinal));

            Goods? singleUsedFuel = null;
            float singleUsedFuelAmount = 0f;
            float bestFuelUsage = float.PositiveInfinity;
            float minEmissions = float.PositiveInfinity;
            int minSize = int.MaxValue;
            float minPower = float.PositiveInfinity;
            float minRecipeTime = float.PositiveInfinity;
            float maxProductivity = 0f;

            Bits recipeUnlockOrder = DataUtils.GetMilestoneOrder(recipe.id);
            List<EntityCrafter> candidateCrafters = [.. recipe.crafters.Where(c => ShouldInclude(c)
                && DataUtils.GetMilestoneOrder(c.id).CompareTo(recipeUnlockOrder) <= 0)];
            if (candidateCrafters.Count == 0) {
                // Fallback: if no crafter is available by the exact unlock step, use any included crafter.
                candidateCrafters = [.. recipe.crafters.Where(ShouldInclude)];
            }

            foreach (var crafter in candidateCrafters) {
                ModuleEffects moduleEffects = default;
                if (TryGetAutoModuleEffects(project, recipe, crafter, out ModuleEffects configuredEffects)) {
                    moduleEffects = configuredEffects;
                }

                float productivity = moduleEffects.productivity;
                if (recipe.maximumProductivity is float maxRecipeProd && productivity > maxRecipeProd) {
                    productivity = maxRecipeProd;
                }
                maxProductivity = MathF.Max(maxProductivity, productivity);

                float recipeTime = recipe.time / crafter.baseCraftingSpeed;
                recipeTime /= moduleEffects.speedMod;
                minRecipeTime = MathF.Min(minRecipeTime, recipeTime);

                foreach ((_, float e) in crafter.energy.emissions) {
                    minEmissions = MathF.Min(e, minEmissions);
                }

                if (crafter.size < minSize) {
                    minSize = crafter.size;
                }

                float power = crafter.energy.type == EntityEnergyType.Void ? 0f : recipe.time * crafter.basePower / (crafter.baseCraftingSpeed * crafter.energy.effectivity);
                power *= moduleEffects.energyUsageMod / moduleEffects.speedMod;
                minPower = MathF.Min(minPower, power);

                // Fuel contribution applies only to non-heat crafters that have non-steam, non-heat fuels.
                if (crafter.energy.type is EntityEnergyType.Heat or EntityEnergyType.FluidHeat) {
                    continue;
                }

                Goods? selectedFuel = crafter.energy.fuels
                    .Where(f => ShouldInclude(f) && !f.isPower && f.fuelValue > 0f && !ExcludeFuelFromCost(f))
                    .OrderBy(f => f, DataUtils.DeterministicComparer)
                    .FirstOrDefault();

                if (selectedFuel == null) {
                    continue;
                }

                float amount = power / selectedFuel.fuelValue;
                if (amount < bestFuelUsage) {
                    bestFuelUsage = amount;
                    singleUsedFuel = selectedFuel;
                    singleUsedFuelAmount = amount;
                }
            }

            if (!float.IsFinite(minPower) || minPower < 0f) {
                minPower = 0f;
            }

            if (!float.IsFinite(minRecipeTime) || minRecipeTime < 0f) {
                minRecipeTime = recipe.time;
            }

            if (!float.IsFinite(minEmissions)) {
                minEmissions = -1f;
            }

            if (minSize == int.MaxValue) {
                minSize = 15;
            }

            int size = Math.Max(minSize, (recipe.ingredients.Length + recipe.products.Length) / 2);
            float sizeUsage = CostPerSecond * minRecipeTime * size;
            float logisticsCost = (sizeUsage * (1f + (CostPerIngredientPerSize * recipe.ingredients.Length) + (CostPerProductPerSize * recipe.products.Length))) + (CostPerMj * minPower);

            // Special handling for spoilage recipes: cost depends on container efficiency and stack size
            // Spoilage happens in storage containers where many stacks spoil in parallel
            if (recipe is Mechanics && recipe.name.StartsWith("spoil.") && recipe.ingredients.Length == 1 && recipe.ingredients[0].goods is Item spoilingItem) {
                int stackSize = spoilingItem.stackSize;
                // Cost is based on storage space needed: time / (stackSize * slotsPerTile)
                // This reflects that larger stacks and better containers reduce infrastructure cost
                logisticsCost = CostPerSecond * minRecipeTime / (stackSize * bestContainerSlotsPerTile);
            }

            if (singleUsedFuel?.isPower == true) {
                singleUsedFuel = null;
            }

            var constraint = workspaceSolver.MakeConstraint(double.NegativeInfinity, 0, recipe.name);
            constraints[recipe] = constraint;

            foreach (var product in recipe.products) {
                var var = variables[product.goods];
                float amount = product.GetAmountPerRecipe(maxProductivity);
                constraint.SetCoefficientCheck(var, amount, ref lastVariable[product.goods]);

                if (product.goods is Item) {
                    logisticsCost += amount * CostPerItem;
                }
                else if (product.goods is Fluid) {
                    logisticsCost += amount * CostPerFluid;
                }
            }

            if (singleUsedFuel != null) {
                var var = variables[singleUsedFuel];
                constraint.SetCoefficientCheck(var, -singleUsedFuelAmount, ref lastVariable[singleUsedFuel]);
            }

            foreach (var ingredient in recipe.ingredients) {
                var var = variables[ingredient.goods]; // TODO split cost analysis
                constraint.SetCoefficientCheck(var, -ingredient.amount, ref lastVariable[ingredient.goods]);

                if (ingredient.goods is Item) {
                    logisticsCost += ingredient.amount * CostPerItem;
                }
                else if (ingredient.goods is Fluid) {
                    logisticsCost += ingredient.amount * CostPerFluid;
                }
            }

            if (recipe.sourceEntity != null && recipe.sourceEntity.mapGenerated) {
                float totalMining = 0f;

                foreach (var product in recipe.products) {
                    totalMining += product.amount;
                }

                float miningPenalty = MiningPenalty;
                float totalDensity = recipe.sourceEntity.mapGenDensity / totalMining;

                if (totalDensity < MiningMaxDensityForPenalty) {
                    float extraPenalty = MathF.Log(MiningMaxDensityForPenalty / totalDensity);
                    miningPenalty += Math.Min(extraPenalty, MiningMaxExtraPenaltyForRarity);
                }

                logisticsCost *= miningPenalty;
            }

            if (minEmissions >= 0f) {
                logisticsCost += minEmissions * CostPerPollution * minRecipeTime * project.settings.PollutionCostModifier;
            }

            if (isFuelGroupConversion) {
                // Fuel-group conversions are normalization helpers, not real-world processing steps.
                logisticsCost = 0f;
            }

            constraint.SetUb(logisticsCost);
            export[recipe] = logisticsCost;
            recipeCost[recipe] = logisticsCost;
        }

        // TODO this is temporary fix for strange item sources (make the cost of item not higher than the cost of its source)
        foreach (Item item in Database.items.all.ExceptExcluded(this)) {
            if (ShouldInclude(item)) {
                foreach (var source in item.miscSources) {
                    if (source is Goods g && ShouldInclude(g)) {
                        var constraint = workspaceSolver.MakeConstraint(double.NegativeInfinity, 0, "source-" + item.locName);
                        constraint.SetCoefficient(variables[g], -1);
                        constraint.SetCoefficient(variables[item], 1);
                    }
                }
            }
        }

        // TODO this is temporary fix for fluid temperatures (make the cost of fluid with lower temp not higher than the cost of fluid with higher temp)
        foreach (var (name, fluids) in Database.fluidVariants) {
            var prev = fluids[0];

            for (int i = 1; i < fluids.Count; i++) {
                var cur = fluids[i];
                var constraint = workspaceSolver.MakeConstraint(double.NegativeInfinity, 0, "fluid-" + name + "-" + prev.temperature);
                constraint.SetCoefficient(variables[prev], 1);
                constraint.SetCoefficient(variables[cur], -1);
                prev = cur;
            }
        }

        if (Database.heatVariants != null) {
            var prev = Database.heatVariants[0];

            for (int i = 1; i < Database.heatVariants.Count; i++) {
                var cur = Database.heatVariants[i];
                var constraint = workspaceSolver.MakeConstraint(double.NegativeInfinity, 0, "heat-" + prev.temperature);
                constraint.SetCoefficient(variables[prev], 1);
                constraint.SetCoefficient(variables[cur], -1);
                prev = cur;
            }
        }

        var result = workspaceSolver.TrySolveWithDifferentSeeds();
        logger.Information("Cost analysis completed in {ElapsedTime}ms with result {result}", time.ElapsedMilliseconds, result);
        float sumImportance = 1f;
        int totalRecipes = 0;

        if (result is Solver.ResultStatus.OPTIMAL or Solver.ResultStatus.FEASIBLE) {
            float objectiveValue = (float)objective.Value();
            logger.Information("Estimated modpack cost: {EstimatedCost}", DataUtils.FormatAmount(objectiveValue * 1000f, UnitOfMeasure.None));
            foreach (Goods g in Database.goods.all.ExceptExcluded(this)) {
                if (variables[g] == null) {
                    continue;
                }

                float value = (float)variables[g].SolutionValue();
                export[g] = value;
            }

            foreach (Recipe recipe in Database.recipes.all.ExceptExcluded(this)) {
                if (constraints[recipe] == null) {
                    continue;
                }

                float recipeFlow = (float)constraints[recipe].DualValue();

                if (recipeFlow > 0f) {
                    totalRecipes++;
                    sumImportance += recipeFlow;
                    flow[recipe] = recipeFlow;
                    foreach (var product in recipe.products) {
                        flow[product.goods] += recipeFlow * product.amount;
                    }
                }
            }
        }
        foreach (FactorioObject o in Database.objects.all.ExceptExcluded(this)) {
            if (!ShouldInclude(o)) {
                export[o] = float.PositiveInfinity;
                continue;
            }

            if (o is RecipeOrTechnology recipe) {
                foreach (var ingredient in recipe.ingredients) // TODO split
{
                    export[o] += export[ingredient.goods] * ingredient.amount;
                }

                foreach (var product in recipe.products) {
                    recipeProductionCost[recipe] += product.amount * export[product.goods];
                }
            }
            else if (o is Entity entity) {
                float minimal = float.PositiveInfinity;

                foreach (var item in entity.itemsToPlace) {
                    if (export[item] < minimal) {
                        minimal = export[item];
                    }
                }
                export[o] = minimal;
            }
        }
        cost = export;
        recipeProductCost = recipeProductionCost;

        // Update fuel group item icons to show the most cost-efficient (lowest cost per MJ) fuel.
        // Only run once (not for the "at current milestones" variant) to avoid redundant updates.
        if (!onlyCurrentMilestones && DataUtils.useFuelGroups) {
            var bestFuelForGroup = new Dictionary<Goods, (Goods fuel, float costPerMj)>();

            foreach (var recipe in Database.recipes.all) {
                if (!recipe.name.StartsWith("fuel-group-recipe.", StringComparison.Ordinal)) {
                    continue;
                }

                if (recipe.ingredients.Length != 1 || recipe.products.Length != 1) {
                    continue;
                }

                Goods fuel = recipe.ingredients[0].goods;
                Goods groupItem = recipe.products[0].goods;
                float costPerMj = fuel.fuelValue > 0f ? cost[fuel] / fuel.fuelValue : float.PositiveInfinity;

                if (!bestFuelForGroup.TryGetValue(groupItem, out var current) || costPerMj < current.costPerMj) {
                    bestFuelForGroup[groupItem] = (fuel, costPerMj);
                }
            }

            foreach (var (groupItem, (bestFuel, _)) in bestFuelForGroup) {
                groupItem.icon = bestFuel.icon;
            }

            // Update conversion recipe icons to also show the best fuel's icon.
            foreach (var recipe in Database.recipes.all) {
                if (!recipe.name.StartsWith("fuel-group-recipe.", StringComparison.Ordinal)) {
                    continue;
                }

                if (recipe.products.Length != 1) {
                    continue;
                }

                Goods groupItem = recipe.products[0].goods;
                if (bestFuelForGroup.TryGetValue(groupItem, out var best)) {
                    recipe.icon = best.fuel.icon;
                }
            }
        }

        recipeWastePercentage = Database.recipes.CreateMapping<float>();
        if (result is Solver.ResultStatus.OPTIMAL or Solver.ResultStatus.FEASIBLE) {
            foreach (var (recipe, constraint) in constraints) {
                if (constraint == null) {
                    continue;
                }

                float productCost = 0f;

                foreach (var product in recipe.products) {
                    productCost += product.amount * export[product.goods];
                }

                recipeWastePercentage[recipe] = 1f - (productCost / export[recipe]);
            }
        }
        else {
            if (!onlyCurrentMilestones) {
                warnings.Error(LSs.CostAnalysisFailed, ErrorSeverity.AnalysisWarning);
            }
        }

        importantItems = [.. Database.goods.all.ExceptExcluded(this).Where(x => x.usages.Length > 1)
            .OrderByDescending(x => flow[x] * cost[x] * x.usages.Count(y => ShouldInclude(y) && recipeWastePercentage[y] == 0f))];

        workspaceSolver.Dispose();
    }

    public static string GetDisplayCost(FactorioObject goods) {
        float cost = goods.Cost();
        float costNow = goods.Cost(true);
        if (float.IsPositiveInfinity(cost)) {
            return LSs.AnalysisNotAutomatable;
        }

        float compareCost = cost;
        float compareCostNow = costNow;
        string finalCost;

        if (goods is Fluid) {
            compareCost = cost * 50;
            compareCostNow = costNow * 50;
            finalCost = LSs.CostAnalysisFluidCost.L(DataUtils.FormatAmount(compareCost, UnitOfMeasure.None));
        }
        else if (goods is Item) {
            finalCost = LSs.CostAnalysisItemCost.L(DataUtils.FormatAmount(compareCost, UnitOfMeasure.None));
        }
        else if (goods is Special special && special.isPower) {
            finalCost = LSs.CostAnalysisEnergyCost.L(DataUtils.FormatAmount(compareCost, UnitOfMeasure.None));
        }
        else if (goods is Recipe) {
            finalCost = LSs.CostAnalysisRecipeCost.L(DataUtils.FormatAmount(compareCost, UnitOfMeasure.None));
        }
        else {
            finalCost = LSs.CostAnalysisGenericCost.L(DataUtils.FormatAmount(compareCost, UnitOfMeasure.None));
        }

        if (compareCostNow > compareCost && !float.IsPositiveInfinity(compareCostNow)) {
            return LSs.CostAnalysisWithCurrentCost.L(finalCost, DataUtils.FormatAmount(compareCostNow, UnitOfMeasure.None));
        }

        return finalCost;
    }

    public static float GetBuildingHours(Recipe recipe, float flow) => recipe.time * flow * (1000f / 3600f);

    public string? GetItemAmount(Goods goods) {
        float itemFlow = flow[goods];
        if (itemFlow <= 1f) {
            return null;
        }

        return itemAmountPrefix + DataUtils.FormatAmount(itemFlow * 1000f, UnitOfMeasure.None);
    }

    private static bool TryGetAutoModuleEffects(Project project, Recipe recipe, EntityCrafter crafter, out ModuleEffects effects) {
        foreach (ProjectModuleTemplate template in project.sharedModuleTemplates) {
            if (TemplateMatches(template, recipe, crafter)) {
                effects = GetTemplateEffects(template.template, recipe, crafter);
                return true;
            }
        }

        if (TryGetFallbackModule(recipe, crafter, out IObjectWithQuality<Module>? fallbackModule)) {
            effects = default;
            effects.AddModules(fallbackModule!, crafter.moduleSlots);
            return true;
        }

        effects = default;
        return false;
    }

    private static bool TemplateMatches(ProjectModuleTemplate projectTemplate, Recipe recipe, EntityCrafter crafter) {
        if (!projectTemplate.autoApplyToNewRows || !projectTemplate.AcceptsEntity(crafter)) {
            return false;
        }

        if (projectTemplate.autoApplyIfIncompatible) {
            return true;
        }

        bool hasFloodfillModules = false;
        bool hasCompatibleFloodfill = false;
        int totalFixedModules = 0;

        foreach (RecipeRowCustomModule module in projectTemplate.template.list) {
            bool isCompatible = recipe.CanAcceptModule(module.module.target) && crafter.CanAcceptModule(module.module);

            if (module.fixedCount == 0) {
                hasFloodfillModules = true;
                hasCompatibleFloodfill |= isCompatible;
            }
            else {
                if (!isCompatible) {
                    return false;
                }

                totalFixedModules += module.fixedCount;
            }
        }

        return (!hasFloodfillModules || hasCompatibleFloodfill) && crafter.moduleSlots >= totalFixedModules;
    }

    private static ModuleEffects GetTemplateEffects(ModuleTemplate template, Recipe recipe, EntityCrafter crafter) {
        ModuleEffects effects = default;
        int remaining = crafter.moduleSlots;

        foreach (RecipeRowCustomModule module in template.list) {
            if (!crafter.CanAcceptModule(module.module) || !recipe.CanAcceptModule(module.module.target)) {
                continue;
            }

            if (remaining <= 0) {
                break;
            }

            int count = Math.Min(module.fixedCount == 0 ? int.MaxValue : module.fixedCount, remaining);
            remaining -= count;
            effects.AddModules(module.module, count);
        }

        if (template.beacon != null) {
            int beaconCount = template.CalculateBeaconCount();
            if (beaconCount > 0) {
                float beaconEfficiency = template.beacon.GetBeaconEfficiency() * template.beacon.target.GetProfile(beaconCount);
                foreach (RecipeRowCustomModule module in template.beaconList) {
                    effects.AddModules(module.module, beaconEfficiency * module.fixedCount);
                }
            }
        }

        return effects;
    }

    private static bool TryGetFallbackModule(Recipe recipe, EntityCrafter crafter, out IObjectWithQuality<Module>? module) {
        module = null;

        if (crafter.allowedModuleCategories is not [string moduleCategory] || crafter.moduleSlots <= 0) {
            return false;
        }

        Bits recipeUnlockOrder = DataUtils.GetMilestoneOrder(recipe.id);
        Module? bestExactModule = null;
        float bestExactSpeed = 0f;

        Module? bestEarlierModule = null;
        float bestEarlierSpeed = 0f;
        Bits bestEarlierUnlockOrder = default;
        bool hasEarlierModule = false;

        foreach (Module candidate in Database.allModules) {
            if (!string.Equals(candidate.moduleSpecification.category, moduleCategory, StringComparison.Ordinal)) {
                continue;
            }

            if (!crafter.CanAcceptModule(candidate.moduleSpecification) || !recipe.CanAcceptModule(candidate)) {
                continue;
            }

            Bits moduleUnlockOrder = DataUtils.GetMilestoneOrder(candidate.id);
            if (moduleUnlockOrder.CompareTo(recipeUnlockOrder) > 0) {
                continue;
            }

            float speed = candidate.moduleSpecification.Speed(Quality.Normal);
            if (moduleUnlockOrder == recipeUnlockOrder) {
                if (speed > bestExactSpeed) {
                    bestExactModule = candidate;
                    bestExactSpeed = speed;
                }
                continue;
            }

            if (!hasEarlierModule || moduleUnlockOrder.CompareTo(bestEarlierUnlockOrder) > 0
                || (moduleUnlockOrder == bestEarlierUnlockOrder && speed > bestEarlierSpeed)) {
                bestEarlierModule = candidate;
                bestEarlierSpeed = speed;
                bestEarlierUnlockOrder = moduleUnlockOrder;
                hasEarlierModule = true;
            }
        }

        Module? selected = bestExactModule ?? bestEarlierModule;
        if (selected == null) {
            return false;
        }

        module = selected.With(Quality.Normal);
        return true;
    }
}
