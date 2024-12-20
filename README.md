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

This sub-project is part of the larger project `Coq-Kruskal` described here: https://github.com/DmxLarchey/Coq-Kruskal.

## Short Description

This library `Kruskal-Veldman` is an extension of [`Kruskal-AlmostFull`](https://github.com/DmxLarchey/Kruskal-AlmostFull)
and [`Kruskal-Higman`](https://github.com/DmxLarchey/Kruskal-Higman) libraries.
It contains a detailed constructive/inductive account 
of Wim Veldman's intuitionistic proofs of a variant of Kruskal's tree theorems \[1\].
Actually the result is [a mixture of Higman's and Kruskal's theorems](#What-is-the-main-result).

From this result, one can easily derive, via simple surjective relational morphisms,
 various forms of Higman's and Kruskal's tree theorems, adapted to the actual implementation 
of rose trees using either lists, or vectors etc. This tasks is devoted to the 
project [`Kruskal-Theorems`](https://github.com/DmxLarchey/Kruskal-Theorems).

\[1\] [_An intuitionistic proof of Kruskal's theorem_](https://link.springer.com/article/10.1007/s00153-003-0207-x), Wim Veldman, 2004

## Target audience

This library is not intended for direct usage, but it is possible to do so. 
Rather, [`Kruskal-Theorems`](https://github.com/DmxLarchey/Kruskal-Theorems) contains the high-level theorems 
that are intended to be used directly.

On the other hand, `Kruskal-Veldman`, in addition of being an intermediate step, was specifically __designed 
to be read/studied__ by those readers who wish to _understand the internal details_ of this difficult
proof. It comes from a major refactoring effort of a [former monolithic Coq proof](https://members.loria.fr/DLarchey/files/Kruskal) 
of the theorem, a project that has been since split into several sub-libraries, initiated after some requests have been formulated 
to access parts of that project specifically. Here is the current split:
- [`Kruskal-Trees`](https://github.com/DmxLarchey/Kruskal-Trees), extra library for lists, vectors, and rose trees; 
- [`Kruskal-Finite`](https://github.com/DmxLarchey/Kruskal-Finite), library to manage finiteness (listability);
- [`Kruskal-AlmostFull`](https://github.com/DmxLarchey/Kruskal-AlmostFull), the basic tools for A(lmost) F(ull) relations (up to Coquand's Ramsey's theorem);
- [`Kruskal-Higman`](https://github.com/DmxLarchey/Kruskal-Higman), the proof of Higman's lemma (or Higman's theorem for unary trees) (see below);
- `Kruskal-Veldman` (in here)
- [`Kruskal-Theorems`](https://github.com/DmxLarchey/Kruskal-Theorems), the proofs of Higman's and [Kruskal's tree theorems](https://en.wikipedia.org/wiki/Kruskal%27s_tree_theorem#:~:text=In%20mathematics%2C%20Kruskal's%20tree%20theorem,quasi%2Dordered%20under%20homeomorphic%20embedding.) for various implementations of bounded and rose trees, and of Vazsonyi's conjecture.

## Usage

To use it directly or via `Kruskal-Theorems`, it can be installed via `opam` after importing the [`coq-opam`](https://github.com/coq/opam)/`released`
package:
```console
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-kruskal-veldman
```
Notice that, as with [`Kruskal-AlmostFull`](https://github.com/DmxLarchey/Kruskal-AlmostFull) (and [`Kruskal-Higman`](https://github.com/DmxLarchey/Kruskal-Higman) btw),
the library comes in `Prop`-bounded and `Type`-bounded flavors, both generated with the very same code base. To access eg. the `Prop`-bounded version
in Coq source code, one should import via:
```coq
From KruskalTrees Require Import idx vec vtree.
From KruskalAfProp Require Import almostfull.
From KruskalVeldmanProp Require Import vtree_embed veldman_theorem.
```

When the intention is to review the code base of `Kruskal-Veldman` with the help of an IDE for the Coq proof assistant, 
the procedure is a bit different. Then it is advised to download the current code base, either via
the [latest release](https://github.com/DmxLarchey/Kruskal-Veldman/releases), or cloning the `main` branch
here, and unpacking it in say the `Kruskal-Veldman` directory.
```console
git clone https://github.com/DmxLarchey/Kruskal-Veldman.git
cd Kruskal-Veldman
```
Then one should install the dependencies via:
```console
opam install . --deps-only
```
and then compile the eg. `Type`-bounded version of the library with:
```console
make type
```
while the `Prop`-bounded version could be obtained via `make prop`. Notice that only one
can be compiled in a given directory because the code base in the same, except from
one selector file `base/base_implem.v` which is copied either from [`implem/prop.v`](theories/implem/prop.v)
or [`implem/type.v`](theories/implem/type.v) depending on `make prop` or `make type`.

Then one can review the code base with say [`CoqIDE`](https://coq.inria.fr/download) 
or [`vscoq`](https://github.com/coq-community/vscoq). But see below for a detailed
introduction on the proof implemented here.

# What is the main result

The main result established here in [`veldman_theorem.v`](theories/universe/veldman_theorem.v) can be stated as follows:
```coq
Variables (A : Type) (k : nat) (X : nat → rel₁ A) (R : nat → rel₂ A).

Inductive vtree_upto_embed : vtree A → vtree A → Prop :=
  | vtree_upto_embed_subt t m y (w : vec _ m) i : t ≤ₖ w⦃i⦄ → t ≤ₖ ⟨y|w⟩
  | vtree_upto_embed_lt n x (v : vec _ n) y w : n < k → R n x y → vec_fall2 (⋅ ≤ₖ ⋅) v w → ⟨x|v⟩ ≤ₖ ⟨y|w⟩
  | vtree_upto_embed_ge n x (v : vec _ n) m y (w : vec _ m) : k ≤ n → R k x y → vec_embed (⋅ ≤ₖ ⋅) v w → ⟨x|v⟩ ≤ₖ ⟨y|w⟩
where "s ≤ₖ t" := (vtree_upto_embed s t).

Theorem afs_vtree_upto_embed :
           (∀n, k ≤ n → X n = X k)
         → (∀n, k ≤ n → R n = R k)
         → (∀n, n ≤ k → afs (X n) (R n))
         → afs (wft X) (⋅ ≤ₖ ⋅).
```
where
- `vtree _` is the type of vector-based uniform `A`-indexed rose trees 
as defined in [`Kruskal-Trees/../vtree.v`](https://github.com/DmxLarchey/Kruskal-Trees/blob/main/theories/tree/vtree.v);
- `afs` is the specialisation of the `af` predicate to sub-types,
as defined in [`Kruskal-AlmostFull/../af.v`](https://github.com/DmxLarchey/Kruskal-AlmostFull/blob/main/theories/af/af.v);
- and [`wft X : vtree A → Prop`](https://github.com/DmxLarchey/Kruskal-Trees/blob/main/theories/tree/vtree.v#L38) 
  is the sub-type of _w(ell) f(ormed) t(rees)_ consisting in those `t : vtree A` such that each sub-tree `⟨x|v⟩` of `t`
  satisfies `X n x` where `n` is the arity, ie the length of `v`. So `X` restricts which labels in `A` can be
  used, not uniformly, but instead, depending on the arity. This variability is critical in the inductive proof;
- also the relation `R` varies according to the arity but this is discussed in more details below.

The nested inductive relation `vtree_upto_embed k R`, also denoted `≤ₖ` for short, is intermediate between
- the product embedding for vectors (cf. [`vec_fall2`](https://github.com/DmxLarchey/Kruskal-Trees/blob/main/theories/vec/vec.v#L481))
used in a nested way in Higman's theorem;
- and the homeomorphic embedding for vectors (cf. [`vec_embed`](https://github.com/DmxLarchey/Kruskal-Higman/blob/main/theories/embeddings/vec_embed.v#L102)) 
used in a nested way in Kruskal's theorem.

The greater the parameter `k`, the closer `≤ₖ` over approximates the product embedding,
while `≤ₖ` also lower approximates the homeomorphic embedding. But when `k = 0`, then `≤ₖ = ≤₀` is exactly the 
homeomorphic embedding.  We recall that the nested product embedding alone is only AF for finitary trees when
their breadth is bounded by constant (here `k`), which explain why it is extended in `≤ₖ` using the homeomorphic
embedding at arities above `k`;

Let us analyze the relation `⟨x|v⟩ ≤ₖ ⟨y|w⟩` in a more procedural way (in contrast with its inductive definition):
1. the first possibility is that `⟨x|v⟩` already `≤ₖ`-embeds into one of the sub-trees `w⦃_⦄` of `⟨y|w⟩`, irrelevant
  of the arities or values of the roots `x` and `y`. This part is common to the embeddings of Higman's and Kruskal's
  theorems;
2. the second possibility applies to small arities (lesser than `k`): in that case, 
  the arities of `v` and `w` are identical (equal to `n`) and `n` is smaller than `k`. 
  Moreover, we must have `v⦃i⦄ ≤ₖ w⦃i⦄` for `i = 1,..,n`, hence this _direct product_ recursively uses
  `≤ₖ` to compare the components of `v` and `w`. Finally the root label `x` must embed into the root label `y` 
  using the relation `R` at index `n`, their common arity. This part mimics the embedding 
  of Higman's theorem, but only for small arities;
3. the third (and last) possibility applies to large arities (greater than `k`): in that
  case, the arity `n` of `v`, that `m` of `w`, and `k` must satisfy `k ≤ n ≤ m`. Notice that
  `n ≤ m` is enforced when stating that `v` vector-embeds into `w` recursively using `≤ₖ` to compare 
  the components. Finally, to compare the roots `x` and `y` which may live at different arities, we
  use the relation `R` at (fixed) index `k`. But any other value above `k` will do since we assume 
  that `R` is stable after index `k`: `R k = R (k+1) = R (k+2) = ...` This part mimics the embedding
  of Kruskal's theorem, however only for large arities.

The proof `afs_vtree_upto_embed`, in plain english that `vtree_upto_embed k R` is AF when all `R₀,...,Rₖ` 
are AF, is the cornerstone of the `Kruskal-*` project series and the most technical/difficult part of this series. 

# How difficult is this proof?

Those who have read Wim Veldman's account \[1\] of Kruskal's tree theorem know
that this proof is very involved, possibly even obscure when one is not
used to intuitionistic set theory where most objects are (encoded as) natural numbers.
Converting that proof to type theory was a project we completed in 2015-2016 and 
[published as a monolithic Coq development](https://members.loria.fr/DLarchey/files/Kruskal).

That former mechanization however was based on _several sub-optimal design choices_ 
(for instance rose trees as nested lists instead of nested vectors) 
or a lack of some abstractions, leading to quite a lot code duplication. 
It gave a Coq-checkable proof script for a nice statement of the tree theorem 
and presented undeniable improvements over the pen&paper proof \[1\]:
- it lifted the proof to a type theoretic settings with
  an inductive formulation of almost full relations;
- it circumvented (and hence solved) the issue of _Church thesis_, 
  which is an axiom used in \[1\] to recovered a _stump_ from a proof 
  of almost-fullness of a relation. Beware that we do not give a proof of Church 
  thesis, we simply avoid its usage.

Still, we could not consider that former monolithic development as a clean enough reference work for 
a less painful learning path into the arguably complicated pen&paper intuitionistic 
account of Kruskal's theorem \[1\]:
- too much proof code (duplication), sub-optimal proof automation;
- too many edge cases, retrospectively due to bad design choices for 
  the Coq implementation of analysis/evaluation;
- as a consequence, too strong hypotheses for the statement of 
  eg. what has now become [`veldman_afs_universe`](theories/universe/veldman_universe.v#L111),
  where, in that former work of ours:
    - we required the decidability of `X : nat → rel₁ A`, but not of `R : nat → rel₂ A` !!
    - we had to carry that extra assumption all along the inductive steps of the proof
      with significant overhead;
    - this additional assumption was related to the implementation choice 
      of the analysis/evaluations as _Coq functions_;
    - they are now converted to a _single relation_, and the decidability 
      requirement could then be _dropped_.

In the current project, via good factorization, proof scripts cleanup 
and abstraction, we think that we provide a much better reference code
for __entering the intimacy of this beautiful proof__, where some novel 
tools are hopefully abstracted at a suitable level.

# The big picture of the proof

We describe the big picture of the proof at the cost of some vagueness here.
At the end of the section, we point out keys aspects than must be refined
before this sketch can be turn into a type-checkable Coq proof.

## The proof sketch

Assuming `k` and relations `R₀⇓X₀,...,Rₖ⇓Xₖ` on sub-types of `A`, of which
neither `k` nor the `Rₙ⇓Xₙ` are fixed, and for which we assume AF
by `afs Xₙ Rₙ` (ie `af Rₙ⇓Xₙ`), we want to show `afs (wft X) (vtree_upto_embed k R)`.
Recall that the `_ ⇓ _` notation denotes the _restriction_ of a relation to a sub-type.

The first step is to proceed by "induction" on the sequence `R₀⇓X₀,...,Rₖ⇓Xₖ`,
but this is not exactly well-founded induction. It would be more accurate to
say that we proceed by induction on the sequence of proofs `afs X₀ R₀,...,afs Xₖ Rₖ`
but we avoid the details at this stage. Also, we skip the description of the order
used for this first induction. We just call it _lexicographic order_ on `afs` predicates.
This gives us our first (informally stated) induction hypothesis as:
```
[IH1]: for any R'₀⇓X'₀,...,R'ₚ⇓X'ₚ st (∀n, afs X'ₙ R'ₙ) 
          and which is lex.-smaller that R₀⇓X₀,...,Rₖ⇓Xₖ,
       we have afs (wft X') (vtree_upto_embed p R')
```
Then, having this first induction hypothesis at our disposal, we want to show 
```coq
afs (wft X) (vtree_upto_embed k R)
```
Applying the second constructor of `afs`, the proof goal becomes 
```coq
∀t₀, wft X t₀ → afs (wft X) (vtree_upto_embed k R)↑t₀
```
We then proceed, in a second (nested) induction, structurally on `t₀`. 
Assuming `t₀ = ⟨α|γ⟩` is of arity `n`, we have new induction hypotheses, 
namely:
```coq
[IH2]: ∀i∈{1,...,n}, afs (wft X) (vtree_upto_embed k R)↑γ⦃i⦄
```

Now there is a case distinction between `n = 0`, `0 < n < k` and `k ≤ n`. When
`n = 0`, ie `t₀ = ⟨α|∅⟩` is a _leaf_, there is a separate treatment which is easier
and we do not discuss it here. In the two other cases, we proceed with a common
overall sketch but the details differ: 
- [`veldman_higman.v`](theories/universe/veldman_higman.v) describes the case `0 < n < k`;
- [`veldman_kruskal.v`](theories/universe/veldman_kruskal.v) describes the case `k ≤ n`.

In both cases we build a new sequence of AF relations `R'₀⇓X'₀,...,R'ₚ⇓X'ₚ`
where possibly `p` might differ from `k`; it can even be larger. 
However, this new sequence is built smaller than `R₀⇓X₀,...,Rₖ⇓Xₖ` 
in the lexicographic order mentioned above. These `R'ₙ⇓X'ₙ` are proved
AF using the second induction hypotheses `[IH2]` and consequences of (Coquand's
formulation of) Ramsey's theorem, ie. closure of AF under binary intersections,
and also, when `k ≤ n`, Higman's lemma for `vec_embed`.

Hence, the first induction hypothesis `[IH1]` gives us 
`afs X' (vtree_upto_embed p R')` and we transfer the AF property
via
```coq
afs (wft X') (vtree_upto_embed p R') → afs (wft X) (vtree_upto_embed k R)↑⟨α|γ⟩
```
using a well chosen [_quasi morphism_](https://github.com/DmxLarchey/Quasi-Morphisms) based on an _analysis/evaluation relation_
between trees in `wft X'` and trees in `wft X`. Which concludes the proof sketch.

## Some key issues that must be refined

Some _key properties_ are not discussed in the above sketch: 
1. to be able to build the new sequence `R'₀⇓X'₀,...,R'ₚ⇓X'ₚ`, the type `A` needs 
   to be equipped with some structure allowing eg. to nest (trees of) itself 
   from within, a bit like universes in set theory. Of course, an arbitrary type
   `A` does not have this property. 
    - in \[1\], the choice is made for `A` to be `nat`, which is
      the natural choice for intuitionistic set theory, but this also limits the main 
      result to `nat`, or to types that must be first embedded into `nat`; 
    - we proceed otherwise: in [`universe.v`](theories/universe/universe.v)
      we first embed an arbitrary type `A` into a richer type `U := universe A` 
     that has the necessary structure for the recursive proofs in 
     [`velman_higman.v`](theories/universe/veldman_higman.v), 
     [`veldman_kruskal`](theories/universe/veldman_kruskal.v) and 
     [`veldman_universe.v`](theories/universe/veldman_universe.v);
    - then, after the recursive proof, we project in [`veldman_theorem.v`](theories/universe/veldman_theorem.v)
      the result for `U := universe A` back to the arbitrary type `A` by a 
      simple surjective morphism, a trivial projection since `U` extends `A`.
2. the lexicographic induction needs extra information about the proof of `afs Xₙ Rₙ`
   to be able to make a case distinction when `Rₙ` is a full relation on `Xₙ`, and
   also when `Xₙ` is an empty sub-type. None of these conditions can be decided. 
   In \[1\], _stumps_ are used for this tasks. But while stumps can be computed
   from `afs Xₙ Rₙ` in the `Type`-bounded case, on the contrary they
   cannot be computed in the `Prop`-bounded case:
    - in \[1\], _Church thesis_ is used specifically for this purpose, but
      the price is of an _assumed axiom_;
    - in here, we _circumvent_ Church thesis by using the (new ?) notion 
      of _well-foundness up to a projection_ which allows us to access 
      the above information (fullness of `Rₙ` or emptiness of `Xₙ`) 
      in the internals of the recursive proof as soon as the output type does not 
      state properties about this (hidden) information.
3. the construction of the "well-chosen quasi-morphism" is somewhat natural but 
   not trivial at all and its properties can be difficult to establish, 
   depending on which framework is used to implement it (eg `list` or `vec` 
   based rose trees). The [`Kruskal-Finite`](https://github.com/DmxLarchey/Kruskal-Finite) library tools
   where specifically designed to allow for manageable proofs that those
   well-chosen quasi-morphisms have finite inverse images.

# How to enter the recursive proof in more details

Our first remark would be: start with _Higman's lemma_ as in 
[`Kruskal-Higman`](https://github.com/DmxLarchey/Kruskal-Higman) which was specifically
designed as a downgrade of the more general cases of the proofs of Higman's theorem 
and Kruskal's tree theorem \[1\]. This proof concerns the restricted case of _unary trees_,
which are just lists with an extra label on the empty list.

It could be made simpler/shorter (but still constructive), 
as done by previous authors like D. Fridlender \[2\], but that was precisely
not the goal. The main goal of [`Kruskal-Higman`](https://github.com/DmxLarchey/Kruskal-Higman)
was to implement the proof sketch and tools 
that are common with that of the current proof of `afs_vtree_upto_embed` above, 
but in a simpler/shorter context.

Once that proof of Higman's lemma is understood, 
the two main innovations for the proof of `afs_vtree_upto_embed` are
as described above:
- the use of a type that we call a [_universe_](theories/universe/universe.v) 
  and which is stable under all the type theoretic constructs that occur
  in the proof;
- the implementation of the [_easier_ and _more facile_](theories/af/afs_lex.v) lexicographic induction 
  principles using the notion of [_well foundness up to a projection_](theories/wf/wf_upto.v), which
  allows to circumvent the use of _Church's thesis_.

The core and technical part of the proof are two files, 
[`veldman_higman.v`](theories/universe/veldman_higman.v) and [`veldman_kruskal.v`](theories/universe/veldman_kruskal.v),
of reasonable size (around 700 loc each), sharing the same structure 
as [`af_utree_embed_fun.v`](https://github.com/DmxLarchey/Kruskal-Higman/blob/main/theories/af/af_utree_embed_fun.v)
from [`Kruskal-Higman`](https://github.com/DmxLarchey/Kruskal-Higman), which we insist, 
should rather be understood first before switching to those two more complicated variations.

To be fair, these two files `veldman_{higman,kruskal}.v` rely heavily on a library for 
the [_insertion_](theories/vec/insert.v) and [_intercalation_](theories/vec/intercal.v) 
of dependent vectors, critically viewed as _dependent inductive relations_, 
and __not__ dependent functions, to avoid the worst setoid hell I ever contemplated.

Recall that during the recursive proof, we want 
to establish that `afs (wft X) (vtree_upto_embed k R)↑t₀`:
- [veldman_higman.v](theories/universe/veldman_higman.v) constructs a quasi-morphism when the lifting tree `t₀`
  has root arity strictly smaller than `k`, the one in the relation `vtree_upto_embed k R` also denoted `≤ₖ` above;
- [veldman_kruskal.v](theories/universe/veldman_kruskal.v) constructs a quasi-morphism when the lifting tree `t₀`
  has root arity greater than `k`;
- also notice that the case of arity 0 for `t₀` is considered in the separate 
  file [veldman_leaves.v](theories/universe/veldman_leaves.v) because it is a
  simpler case for the recursive proof.

\[2\] _Higman's lemma in type theory_, Daniel Fridlender, TYPES 1996

# Well foundness up to a projection

To be completed.
