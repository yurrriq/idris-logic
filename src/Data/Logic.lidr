---
title: Logic
subtitle: An Idris port of Coq.Init.Logic
title-meta: "Logic: An Idris port of Coq.Init.Logic"
author:
- |
  \affaddr{Eric Bailey}\
  \affaddr{https://github.com/yurrriq}\
  \email{eric@ericb.me}
author-meta: Eric Bailey
abstract: Here I present an Idris port of the [`Coq.Init.Logic`](https://coq.inria.fr/library/Coq.Init.Logic.html) module from the Coq standard library.
keywords:
- logic
- coq
- idris
pandoc-minted:
  language: idris
---

> ||| An Idris port of Coq.Init.Logic
> module Logic
>
> import Data.Bifunctor
>
> %access export

= Propositional connectives

== Unit

`()` is the always true proposition ($\top$).

```idris
%elim data Unit = MkUnit
```

== Void

`Void` is the always false proposition ($\bot$).

```idris
%elim data Void : Type where
```

== Negation

`Not a`, written `~a`, is the negation of `a`.

> syntax "~" [x] = (Not x)

```idris
Not : Type -> Type
Not a = a -> Void
```

== Conjunction

`And a b`, written `(a, b)`, is the conjunction of `a` and `b`.

`Conj p q` is a proof of `(a, b)` as soon as `p` is a proof of `a` and `q` a proof of `b`.

`proj1` and `proj2` are first and second projections of a conjunction.

> syntax "(" [a] "," [b] ")" = (And a b)
>
> ||| The conjunction of `a` and `b`.
> data And : Type -> Type -> Type where
>      Conj : a -> b -> (a, b)
>
> implementation Bifunctor And where
>     bimap f g (Conj a b) = Conj (f a) (g b)
>
> ||| First projection of a conjunction.
> proj1 : (a, b) -> a
> proj1 (Conj a _) = a
>
> ||| Second projection of a conjunction.
> proj2 : (a, b) -> b
> proj2 (Conj _ b) = b

== Disjunction

`Either a b` is the disjunction of `a` and `b`.

```idris
data Either : Type -> Type -> Type where
     Left   : a -> Either a b
     Right  : b -> Either a b     
```

== Biconditional

[Proof Wiki](https://proofwiki.org/wiki/Definition:Biconditional)

 <!-- $\varphi \vdash \psi$\ -->
 <!-- $\underline{\psi \vdash \varphi}$\ -->
 <!-- $\varphi \iff \psi$ -->

`iff a b`, written `a <-> b`, expresses the equivalence of `a` and `b`.

> infixl 9 <->
>
> ||| The biconditional is a *binary connective* that can be voiced:
> ||| *p* **if and only if** *q*.
> public export
> (<->) : Type -> Type -> Type
> (<->) a b = (a -> b, b -> a)

=== Biconditional is Reflexive

[Proof Wiki](https://proofwiki.org/wiki/Biconditional_is_Reflexive)

$\vdash \varphi \iff \varphi$

> ||| The biconditional operator is reflexive.
> iffRefl : a <-> a
> iffRefl = Conj id id

=== Biconditional is Transitive

[Proof Wiki](https://proofwiki.org/wiki/Biconditional_is_Transitive)

 <!-- \[ -->
 <!--   \begin{prooftree} -->
 <!--     \Hypo{ \varphi \iff \psi } -->
 <!--     \Hypo{ \psi \iff \chi } -->
 <!--     \Infer2 { \vdash \varphi \iff \chi } -->
 <!--   \end{prooftree} -->
 <!-- \] -->

> ||| The biconditional operator is transitive.
> iffTrans : (a <-> b) -> (b <-> c) -> (a <-> c)
> iffTrans (Conj ab ba) (Conj bc cb) =
>     Conj (bc . ab) (ba . cb)

=== Biconditional is Commutative

[Proof Wiki](https://proofwiki.org/wiki/Biconditional_is_Commutative)

$\varphi \iff \psi \dashv\vdash \psi \iff \varphi$

or

$\vdash (\varphi \iff \psi) \iff (\psi \iff \varphi)$

> ||| The biconditional operator is commutative.
> iffSym : (a <-> b) -> (b <-> a)
> iffSym (Conj ab ba) = Conj ba ab

=== andIffCompatLeft

$\psi \iff \chi \dashv\vdash (\varphi \land \psi) \iff (\varphi \land \chi)$

> andIffCompatLeft : (b <-> c) -> ((a, b) <-> (a, c))
> andIffCompatLeft = bimap second second

=== andIffCompatRight

$\psi \iff \chi \dashv\vdash (\psi \land \varphi) \iff (\chi \land \varphi)$

> andIffCompatRight : (b <-> c) -> ((b, a) <-> (c, a))
> andIffCompatRight = bimap first first

=== orIffCompatLeft

$\psi \iff \chi \vdash (\varphi \lor \psi) \iff (\varphi \lor \chi)$

> orIffCompatLeft : (b <-> c) ->
>                   (Either a b <-> Either a c)
> orIffCompatLeft = bimap second second

=== orIffCompatRight

$\psi \iff \chi \vdash (\psi \lor \varphi) \iff (\chi \lor \varphi)$

> orIffCompatRight : (b <-> c) ->
>                    (Either b a <-> Either c a)
> orIffCompatRight = bimap first first

=== negVoid

$\neg \varphi \dashv\vdash \varphi \iff \bot$

or

$\vdash \neg \varphi \iff (\varphi \iff \bot)$

> negVoid : (~a) <-> (a <-> Void)
> negVoid = Conj (flip Conj void) proj1

=== andCancelLeft

 <!-- $\psi \implies \varphi$\ -->
 <!-- $\underline{\chi \implies \varphi}$\ -->
 <!-- $((\varphi \land \psi) \iff (\varphi \land \chi)) \iff (\psi \iff \chi)$ -->

> andCancelLeft : (b -> a) ->
>                 (c -> a) ->
>                 (((a, b) <-> (a, c)) <-> (b <-> c))
> andCancelLeft ba ca = Conj (bimap f g) andIffCompatLeft
>   where
>     f h b = proj2 . h $ Conj (ba b) b
>     g h c = proj2 . h $ Conj (ca c) c

=== andCancelRight

> andCancelRight : (b -> a) ->
>                  (c -> a) ->
>                  (((b, a) <-> (c, a)) <-> (b <-> c))
> andCancelRight ba ca = Conj (bimap f g) andIffCompatRight
>   where
>     f h b = proj1 . h $ Conj b (ba b)
>     g h c = proj1 . h $ Conj c (ca c)

=== Conjunction is Commutative

[Proof Wiki](https://proofwiki.org/wiki/Rule_of_Commutation/Conjunction)

==== Formulation 1
$\varphi \land \psi \dashv\vdash \psi \land \varphi$

==== Formulation 2
$\vdash (\varphi \land \psi) \iff (\psi \land \varphi)$

==== Source

> ||| Conjunction is commutative.
> andComm : (a, b) <-> (b, a)
> andComm = Conj swap swap
>   where
>     swap : (p, q) -> (q, p)
>     swap (Conj p q) = Conj q p

=== Conjunction is Associative

[Proof Wiki](https://proofwiki.org/wiki/Rule_of_Association/Conjunction)

==== Formulation 1
$(\varphi \land \psi) \land \chi \dashv\vdash \varphi \land (\psi \land \chi)$

==== Formulation 2
$\vdash ((\varphi \land \psi) \land \chi) \iff (\varphi \land (\psi \land \chi))$

==== Source

> ||| Conjunction is associative.
> andAssoc : ((a, b), c) <-> (a, (b, c))
> andAssoc = Conj f g
>   where
>     f abc@(Conj (Conj a b) c) = Conj a (first proj2 abc)
>     g abc@(Conj a (Conj b c)) = Conj (second proj1 abc) c

=== orCancelLeft

$(\psi \implies \neg \varphi) \implies (\chi \implies \neg \varphi) \implies (((\varphi \lor \psi) \iff (\varphi \lor \chi)) \iff (\psi \iff \chi))$

> orCancelLeft : (b -> ~a) ->
>                (c -> ~a) ->
>                ((Either a b <-> Either a c) <-> (b <-> c))
> orCancelLeft bNotA cNotA = Conj (bimap f g) orIffCompatLeft
>   where
>     f ef b = go (bNotA b) (ef (Right b))
>     g eg c = go (cNotA c) (eg (Right c))
>     go : (~a) -> Either a b -> b
>     go lf = either (void . lf) id

=== orCancelRight

 <!-- $\psi \vdash \neg \varphi$\ -->
 <!-- $\underline{\chi \vdash \neg \varphi}$\ -->
 <!-- $((\psi \lor \varphi) \iff (\chi \lor \varphi)) \iff (\psi \iff \chi)$ -->

> orCancelRight : (b -> ~a) ->
>                 (c -> ~a) ->
>                 ((Either b a <-> Either c a) <-> (b <-> c))
> orCancelRight bNotA cNotA = Conj (bimap f g) orIffCompatRight
>   where
>     f ef b = go (bNotA b) (ef (Left b))
>     g eg c = go (cNotA c) (eg (Left c))
>     go : (~p) -> Either q p -> q
>     go rf = either id (void . rf)

=== Disjunction is Commutative

[Proof Wiki](https://proofwiki.org/wiki/Rule_of_Commutation/Disjunction)

$(\varphi \lor \psi) \iff (\psi \lor \varphi)$

> ||| Disjunction is commutative.
> orComm : Either a b <-> Either b a
> orComm = Conj mirror mirror

=== Disjunction is Associative

[Proof Wiki](https://proofwiki.org/wiki/Rule_of_Association/Disjunction)

$(\varphi \lor \psi) \lor \chi \vdash \varphi \lor (\psi \lor \chi)$

> ||| Disjunction is associative on the left.
> orAssocLeft : Either (Either a b) c -> Either a (Either b c)
> orAssocLeft = either (second Left) (pure . pure)

$\varphi \lor (\psi \lor \chi) \vdash (\varphi \lor \psi) \lor \chi$

> ||| Disjunction is associative on the right.
> orAssocRight : Either a (Either b c) -> Either (Either a b) c
> orAssocRight = either (Left . Left) (first Right)

==== Formulation 1
$(\varphi \lor \psi) \lor \chi \dashv\vdash \varphi \lor (\psi \lor \chi)$

==== Formulation 2
$\vdash ((\varphi \lor \psi) \lor \chi) \iff (\varphi \lor (\psi \lor \chi))$

==== Source

> ||| Disjunction is associative.
> orAssoc : Either (Either a b) c <-> Either a (Either b c)
> orAssoc = Conj orAssocLeft orAssocRight

=== iffAnd

$\varphi \iff \psi \vdash (\varphi \implies \psi) \land (\psi \implies \varphi)$

> iffAnd : (a <-> b) -> (a -> b, b -> a)
> iffAnd = id

=== iffAndTo

$\varphi \iff \psi \dashv\vdash (\varphi \implies \psi) \land (\psi \implies \varphi)$

or

$\vdash (\varphi \iff \psi) \iff ((\varphi \implies \psi) \land (\psi \implies \varphi))$

> iffToAnd : (a <-> b) <-> (a -> b, b -> a)
> iffToAnd = Conj id id
