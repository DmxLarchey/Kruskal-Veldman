```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)
```

# What is this library?

This library is an extension of [`Kruskal-AlmostFull`](https://github.com/DmxLarchey/Kruskal-AlmostFull).
It contains a detailed constructive/inductive account 
of Wim Veldman's intuitionistic proofs of
Higman's and Kruskal tree theorems \[1\].
The main result established here can be stated as follows:
```coq
Variables (A : Type) (k : nat) (X : nat → rel₁ A) (R : nat → rel₂ A).

Inductive vtree_upto_embed : vtree A → vtree A → Prop :=
  | vtree_upto_embed_subt t n x (v : vec _ n) i : t ≤ₖ v⦃i⦄ → t ≤ₖ ⟨x|v⟩
  | vtree_upto_embed_lt n x (v : vec _ n) y w : n < k → R n x y → vec_fall2 (⋅ ≤ₖ ⋅) v w → ⟨x|v⟩ ≤ₖ ⟨y|w⟩
  | vtree_upto_embed_ge n x (v : vec _ n) m y (w : vec _ m) : k ≤ n → R k x y → vec_embed (⋅ ≤ₖ ⋅) v w → ⟨x|v⟩ ≤ₖ ⟨y|w⟩
where "s ≤ₖ t" := (vtree_upto_embed s t).

Theorem afs_vtree_upto_embed :
           (∀n, k ≤ n → X n = X k)
         → (∀n, k ≤ n → R n = R k)
         → (∀n, n ≤ k → afs (X n) (R n))
         → afs (wft X) (⋅ ≤ₖ ⋅).
```
where `vtree _` is the type of vector-based uniform `A`-indexed rose trees 
(as defined in [`Kruskal-Trees/../vtree.v`](https://github.com/DmxLarchey/Kruskal-Trees/blob/main/theories/tree/vtree.v)
and `afs` is the specialisation of the `af` predicate to sub-types
(as defined in [`Kruskal-AlmostFull/../af.v`](https://github.com/DmxLarchey/Kruskal-AlmostFull/blob/main/theories/af/af.v).

The nested inductive relation `vtree_upto_embed k R`, also denoted `≤ₖ` for short, is intermediate between
the nested product (cf. `vec_fall2`) embedding of Higman's theorem (which is only AF for trees of bounded breadth),
and the homeomorphic (cf. `vec_embed`) embedding of Kruskal's theorem. The greater the parameter `k`, the closer
`≤ₖ` over approximates the product embedding, while `≤ₖ` also lower approximates the homeomorphic embedding.
But when `k = 0`, then `≤ₖ` is exactly the homeomorphic embedding.

This proof is the cornerstone of the `Kruskal-*` project series and the most technical/difficult
part of this series. From this result, one can easily derives various forms of Kruskal's tree
theorem, depending on the actual implementation of rose trees using lists, vectors etc. This
tasks is devoted to the upcoming project `Kruskal-Theorems`, to be published as a follow-up on
short notice.

\[1\]. [_An intuitionistic proof of Kruskal's theorem_](https://link.springer.com/article/10.1007/s00153-003-0207-x), Wim Veldman, 2004

# How difficult is this proof?

Those who have read Wim Veldman's intuitionistic proof \[1\] of Kruskal's tree theorem know
that this proof is very involved. Converting that proof to type theory was a project we
completed in 2015-2016 and [published as a monolithic Coq project here](https://members.loria.fr/DLarchey/files/Kruskal).

That former proof however was based on _several sub-optimal design choices_ 
(for instance rose trees as nested lists instead of nested vectors) 
or a lack of some abstractions, leading to quite a lot code duplication. 
It gave a Coq-checkable proof script for a nice statement of the tree theorem 
and presented undeniable improvements over the pen&paper proof:
- compared to \[1\], it lifts the proof to a type theoretic settings with
  an inductive formulation of almost full relations;
- it solved the issue of _Church thesis_, which is an axiom used in \[1\]
  to recovered a _stump_ from a proof of almost-fullness of a relation;

Still, we could not consider it as a clean enough reference work for 
a quicker learning path into this apparently complicated pen&paper proof:
- too much proof code (duplication), sub-optimal proof automation;
- too many edge cases, retrospectively due to bad design choices for 
  the Coq implementation of analysis/evaluation;
- as a consequence, too strong hypotheses for the statement of 
  eg. `afs_vtree_upto_embed` where:
    - we required the decidability of `X : nat → rel₁ A`, but not of `R : nat → rel₂ A` !!
    - we had to carry that extra assumption all along the proof with significant overhead;
    - this additional assumption was related to the implementation choice 
      of the analysis/evaluations as a Coq functions;
    - they are now converted to a single relation, and the decidability 
      requirement has been be dropped.

In the current project, via good factorization, proof scripts cleanup 
and abstraction, we think that we provide a much better reference code
for entering the _intimacy of this beautiful proof_, where some novel 
tools are hopefully abstracted at a suitable level.

# How to enter this proof?

Our first remark would be: start with _Higman's lemma_ as in 
[`Kruskal-Higman`](https://github.com/DmxLarchey/Kruskal-Higman) which was specifically
designed as a downgrade of the more general cases of the proofs of Higman's theorem 
and Kruskal's tree theorem \[1\]. The proof is downgraded to the cases of _at most unary trees_,
which are nearly as simple as lists. The proof there could be made simpler,
as done by previous authors like D. Fridlender or Monica Seisenberger, by that is
not the point. The point is to introduce a proof sketch and tools that are
shared with that of the current proof, but in a simpler/shorter context.

Then, the two main innovations for the proof of `afs_vtree_upto_embed` above are:
- the use of a type that we call a [_universe_](theories/universe/universe.v) 
  and which is stable under all the type theoretic constructs that occur
  in the proof. In \[1\], this type is that of `nat` (natural numbers) in
  which all data-structures are implemented. In our generalization, we
  build a universe as an inductive type extending the start type `A` above;
- the implementation of the [_easier_ and _more facile_](theories/af/afs_lex.v) lexicographic induction 
  principles using the notion of [_well foundness up to a projection_](theories/wf/wf_upto.v), which
  allows to circumvent the use of _Church's thesis_.

The core and technical part of the proof are two files, 
[veldman_higman.v](theories/universe/veldman_higman.v) and [veldman_kruskal.v](theories/universe/veldman_kruskal.v),
of reasonable size (around 700 loc each), sharing the same structure 
as [af_tree_embed_fun.v](https://github.com/DmxLarchey/Kruskal-Higman/blob/main/theories/af/af_utree_embed_fun.v)
from [`Kruskal-Higman`](https://github.com/DmxLarchey/Kruskal-Higman), which, I reiterate, should be understood
first before switching to those two more complicated variations.

Recall that during the recursive proof, we want 
to establish that `afs (wft X) (vtree_upto_embed k R)↑t₀`:
- [veldman_higman.v](theories/universe/veldman_higman.v) constructs a quasi-morphism when the lifting tree `t₀`
  has root arity strictly smaller than the `k`, the one in the relation `vtree_upto_embed k R` also denoted `≤ₖ` above;
- [veldman_kruskal.v](theories/universe/veldman_kruskal.v) constructs a quasi-morphism when the lifting tree `t₀`
  has root arity greater than `k`;
- also notice that the case of arity 0 for `t₀` is considered in the separate 
  file [veldman_leaves.v](theories/universe/veldman_leaves.v) because it is a ground case for the recursive proof.

# Explanations about well foundness up to a projection

To be completed.
