I'm writing to launch the [∞-Cosmos Project](https://emilyriehl.github.io/infinity-cosmos/) which aims to formalize the basic formal theory of ∞-categories in Lean.

The term **∞-cosmos** refers to an axiomatization of the universe in which ∞-categories live as objects. The axioms are somewhat ad-hoc and chosen for largely pragmatic reasons. In particular, the axioms are stated in the language of 1-category theory and simplicially enriched category theory, rather than in the language of ∞-category theory itself. The notion of ∞-cosmoi enables a "model-independent" development of the theory of ∞-categories, since various models such as quasi-categories and complete Segal spaces assemble into ∞-cosmoi.

Much of the development of the theory of ∞-categories takes place not in the full ∞-cosmos but in a quotient 2-category whose objects are ∞-categories, whose morphisms are ∞-functors, and whose 2-cells are ∞-natural transformations. We call this the **homotopy 2-category** since it is a quotient of the ∞-cosmos (which is an (∞,2)-category of a particular form) much like an (∞,1)-category has a quotient homotopy (1-)category. For instance, the existing Mathlib notions of equivalences and adjunctions in a bicategory specialize to define equivalences and adjunctions between ∞-categories when interpreted in the homotopy 2-category.

The initial aims of this project are relatively modest, though with sufficient interest its ambitions could expand considerably. In particular, our initial intention is not to attempt the difficult theorem of proving that the cartesian closed category of quasi-categories defines an example of an ∞-cosmos (among other things, the cartesian closure of this subcategory has not yet been proven) but rather create a large "bounty" to reward anyone who succeeds in this task in the form of a large cache of ∞-categorical theorems that will follow immediately.

This project is being co-lead by @**Dom Verity** and @**Mario Carneiro**, though my hope is to spare them some of the day-to-day burdens by serving as project manager. I'm relatively new to Lean, however, so advice from more experienced folks is **especially welcome.**

If you're interesting in hearing more or contributing to the development of this project, please join us in the #**InfinityCosmos** stream!



**Warm-up definitions**:

D1. Define the [homotopy coherent isomorphism](https://emilyriehl.github.io/infinity-cosmos/blueprint/sec-simplicial-sets.html#defn:coherent-isomorphism). We may later opt to work with different models of this simplicial set.

D2. Define the notion of [isofibration](https://emilyriehl.github.io/infinity-cosmos/blueprint/sec-simplicial-sets.html#defn:qcat-isofibration) between quasi-categories.

D3. Define the notion of [equivalence](https://emilyriehl.github.io/infinity-cosmos/blueprint/sec-simplicial-sets.html#defn:qcat-equivalence) between quasi-categories.

D4. Define the notion of [trivial fibration](https://emilyriehl.github.io/infinity-cosmos/blueprint/sec-simplicial-sets.html#defn:qcat-trivial-fibration) between quasi-categories.

**Tasks involving simplicial sets**:

S1. Define the [homotopy relation on 1-simplices](https://emilyriehl.github.io/infinity-cosmos/blueprint/sec-simplicial-sets.html#defn:1-simplex-htpy) in a simplicial set. Note a draft of this exists written by @**Joseph Tooby-Smith** in a [mathlib PR](https://github.com/leanprover-community/mathlib4/pull/10006/files#diff-d9401595c03bcfddf1ecc22aa64fe6a62f82ae75b237ef92269c4c42f967f04f), though it's not obvious to me which version of this definition will be the most useful.

S2. Prove the [simpler form](https://emilyriehl.github.io/infinity-cosmos/blueprint/sec-simplicial-sets.html#lem:qcat-1-simplex-htpy) of the homotopy relation, under the hypothesis that the ambient simplicial set is a quasi-category. This is really a sequence of lemmas, some of which are already proven in the PR mentioned above.

S3. Characterize the [homotopy category of a quasi-category](https://emilyriehl.github.io/infinity-cosmos/blueprint/sec-simplicial-sets.html#lem:htpy-cat-of-qcat). The general homotopy category functor on simplicial sets has a simplified description on quasi-categories.

S4. Prove that the [homotopy category functor preserves equivalences](https://emilyriehl.github.io/infinity-cosmos/blueprint/sec-simplicial-sets.html#lem:qcat-htpy-cat-equiv).

S5. A final particularly hard task: prove that the homotopy category functor [preserves products](https://emilyriehl.github.io/infinity-cosmos/blueprint/sec-simplicial-sets.html#lem:ho-preserves-products). There are two lemmas here, both of which we will eventually need. I suspect the easier will be to show that the homotopy category functor, when restricted to the subcategory of quasi-categories preserves all products, though this relies on task 3. The harder result, which could be attempted now, would be to show that this functor preserves finite products (binary products and the terminal object) of arbitrary simplicial sets.

**Tasks involving simplicially enriched limits**:

L1. Define [simplicial cotensors](https://emilyriehl.github.io/infinity-cosmos/blueprint/sec-enriched-limits.html#defn:simplicial-cotensor). Note the current definition of "has cotensors" is too weak and should be fixed.

L2. Prove that simplicial cotensors define a [bifunctor](https://emilyriehl.github.io/infinity-cosmos/blueprint/sec-enriched-limits.html#lem:cotensor-bifunctor).

L3. Define [simplicial conical limits](https://emilyriehl.github.io/infinity-cosmos/blueprint/sec-enriched-limits.html#defn:simplicial-conical-limit).

**Tasks involving ∞-cosmoi**:

C1. Using all of the above, complete the definition of an [∞-cosmos](https://emilyriehl.github.io/infinity-cosmos/blueprint/sec-cosmos.html#defn:cosmos).

C2. Define [cartesian closed ∞-cosmoi](https://emilyriehl.github.io/infinity-cosmos/blueprint/sec-cosmos.html#defn:closed-cosmos)
