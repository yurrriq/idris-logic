```idris
||| An Idris port of Coq.Init.Logic
module Logic

import Data.Bifunctor

%access export
```
Propositional connectives
=========================

Unit
----

`()` is the always true proposition (⊤).

```idris
%elim data Unit = MkUnit
```
Void
----

`Void` is the always false proposition (⊥).

```idris
%elim data Void : Type where
```
Negation
--------

`Not a`, written `~a`, is the negation of `a`.

```idris
syntax "~" [x] = (Not x)
```
```idris
Not : Type -> Type
Not a = a -> Void
```
Conjunction
-----------

`And a b`, written `(a, b)`, is the conjunction of `a` and `b`.

`Conj p q` is a proof of `(a, b)` as soon as `p` is a proof of `a` and `q` a proof of `b`.

`proj1` and `proj2` are first and second projections of a conjunction.

```idris
syntax "(" [a] "," [b] ")" = (And a b)

data And : Type -> Type -> Type where
     Conj : a -> b -> (a, b)

implementation Bifunctor And where
    bimap f g (Conj a b) = Conj (f a) (g b)

proj1 : (a, b) -> a
proj1 (Conj a _) = a

proj2 : (a, b) -> b
proj2 (Conj _ b) = b
```
Disjunction
-----------

`Either a b` is the disjunction of `a` and `b`.

```idris
data Either : Type -> Type -> Type where
     Left   : a -> Either a b
     Right  : b -> Either a b     
```
Biconditional
-------------

<!-- $\varphi \vdash \psi$\ --> <!-- $\underline{\psi \vdash \varphi}$\ --> <!-- $\varphi \iff \psi$ -->

`iff a b`, written `a <-> b`, expresses the equivalence of `a` and `b`.

```idris
infixl 9 <->

public export
(<->) : Type -> Type -> Type
(<->) a b = (a -> b, b -> a)
```
### Biconditional is Reflexive

[Proof Wiki](https://proofwiki.org/wiki/Biconditional_is_Reflexive)

⊢*φ* ⇔ *φ*

```idris
iffRefl : a <-> a
iffRefl = Conj id id
```
### Biconditional is Transitive

[Proof Wiki](https://proofwiki.org/wiki/Biconditional_is_Transitive)

<!-- \[ --> <!--   \begin{prooftree} --> <!--     \Hypo{ \varphi \iff \psi } --> <!--     \Hypo{ \psi \iff \chi } --> <!--     \Infer2 { \vdash \varphi \iff \chi } --> <!--   \end{prooftree} --> <!-- \] -->

```idris
iffTrans : (a <-> b) -> (b <-> c) -> (a <-> c)
iffTrans (Conj ab ba) (Conj bc cb) =
    Conj (bc . ab) (ba . cb)
```
### Biconditional is Commutative

[Proof Wiki](https://proofwiki.org/wiki/Biconditional_is_Commutative)

*φ* ⇔ *ψ* ⊣ ⊢*ψ* ⇔ *φ*

or

⊢(*φ* ⇔ *ψ*)⇔(*ψ* ⇔ *φ*)

```idris
iffSym : (a <-> b) -> (b <-> a)
iffSym (Conj ab ba) = Conj ba ab
```
### andIffCompatLeft

*ψ* ⇔ *χ* ⊣ ⊢(*φ* ∧ *ψ*)⇔(*φ* ∧ *χ*)

```idris
andIffCompatLeft : (b <-> c) -> ((a, b) <-> (a, c))
andIffCompatLeft = bimap second second
```
### andIffCompatRight

*ψ* ⇔ *χ* ⊣ ⊢(*ψ* ∧ *φ*)⇔(*χ* ∧ *φ*)

```idris
andIffCompatRight : (b <-> c) -> ((b, a) <-> (c, a))
andIffCompatRight = bimap first first
```
### orIffCompatLeft

*ψ* ⇔ *χ* ⊢ (*φ* ∨ *ψ*)⇔(*φ* ∨ *χ*)

```idris
orIffCompatLeft : (b <-> c) ->
                  (Either a b <-> Either a c)
orIffCompatLeft = bimap second second
```
### orIffCompatRight

*ψ* ⇔ *χ* ⊢ (*ψ* ∨ *φ*)⇔(*χ* ∨ *φ*)

```idris
orIffCompatRight : (b <-> c) ->
                   (Either b a <-> Either c a)
orIffCompatRight = bimap first first
```
### negVoid

¬*φ* ⊣ ⊢*φ* ⇔ ⊥

or

⊢¬*φ* ⇔ (*φ* ⇔ ⊥)

```idris
negVoid : (~a) <-> (a <-> Void)
negVoid = Conj (flip Conj void) proj1
```
### andCancelLeft

<!-- $\psi \implies \varphi$\ --> <!-- $\underline{\chi \implies \varphi}$\ --> <!-- $((\varphi \land \psi) \iff (\varphi \land \chi)) \iff (\psi \iff \chi)$ -->

```idris
andCancelLeft : (b -> a) ->
                (c -> a) ->
                (((a, b) <-> (a, c)) <-> (b <-> c))
andCancelLeft ba ca = Conj (bimap f g) andIffCompatLeft
  where
    f h b = proj2 . h $ Conj (ba b) b
    g h c = proj2 . h $ Conj (ca c) c
```
### andCancelRight

```idris
andCancelRight : (b -> a) ->
                 (c -> a) ->
                 (((b, a) <-> (c, a)) <-> (b <-> c))
andCancelRight ba ca = Conj (bimap f g) andIffCompatRight
  where
    f h b = proj1 . h $ Conj b (ba b)
    g h c = proj1 . h $ Conj c (ca c)
```
### Conjunction is Commutative

[Proof Wiki](https://proofwiki.org/wiki/Rule_of_Commutation/Conjunction)

#### Formulation 1

*φ* ∧ *ψ* ⊣ ⊢*ψ* ∧ *φ*

#### Formulation 2

⊢(*φ* ∧ *ψ*)⇔(*ψ* ∧ *φ*)

#### Source

```idris
andComm : (a, b) <-> (b, a)
andComm = Conj swap swap
  where
    swap : (p, q) -> (q, p)
    swap (Conj p q) = Conj q p
```
### Conjunction is Associative

[Proof Wiki](https://proofwiki.org/wiki/Rule_of_Association/Conjunction)

#### Formulation 1

(*φ* ∧ *ψ*)∧*χ* ⊣ ⊢*φ* ∧ (*ψ* ∧ *χ*)

#### Formulation 2

⊢((*φ* ∧ *ψ*)∧*χ*)⇔(*φ* ∧ (*ψ* ∧ *χ*))

#### Source

```idris
andAssoc : ((a, b), c) <-> (a, (b, c))
andAssoc = Conj f g
  where
    f abc@(Conj (Conj a b) c) = Conj a (first proj2 abc)
    g abc@(Conj a (Conj b c)) = Conj (second proj1 abc) c
```
### orCancelLeft

(*ψ* ⟹ ¬*φ*)⟹(*χ* ⟹ ¬*φ*)⟹(((*φ* ∨ *ψ*)⇔(*φ* ∨ *χ*)) ⇔ (*ψ* ⇔ *χ*))

```idris
orCancelLeft : (b -> ~a) ->
               (c -> ~a) ->
               ((Either a b <-> Either a c) <-> (b <-> c))
orCancelLeft bNotA cNotA = Conj (bimap f g) orIffCompatLeft
  where
    f ef b = go (bNotA b) (ef (Right b))
    g eg c = go (cNotA c) (eg (Right c))
    go : (~a) -> Either a b -> b
    go lf = either (void . lf) id
```
### orCancelRight

<!-- $\psi \vdash \neg \varphi$\ --> <!-- $\underline{\chi \vdash \neg \varphi}$\ --> <!-- $((\psi \lor \varphi) \iff (\chi \lor \varphi)) \iff (\psi \iff \chi)$ -->

```idris
orCancelRight : (b -> ~a) ->
                (c -> ~a) ->
                ((Either b a <-> Either c a) <-> (b <-> c))
orCancelRight bNotA cNotA = Conj (bimap f g) orIffCompatRight
  where
    f ef b = go (bNotA b) (ef (Left b))
    g eg c = go (cNotA c) (eg (Left c))
    go : (~p) -> Either q p -> q
    go rf = either id (void . rf)
```
### Disjunction is Commutative

[Proof Wiki](https://proofwiki.org/wiki/Rule_of_Commutation/Disjunction)

(*φ* ∨ *ψ*)⇔(*ψ* ∨ *φ*)

```idris
orComm : Either a b <-> Either b a
orComm = Conj mirror mirror
```
### Disjunction is Associative

[Proof Wiki](https://proofwiki.org/wiki/Rule_of_Association/Disjunction)

(*φ* ∨ *ψ*)∨*χ* ⊢ *φ* ∨ (*ψ* ∨ *χ*)

```idris
orAssocLeft : Either (Either a b) c -> Either a (Either b c)
orAssocLeft = either (second Left) (pure . pure)
```
*φ* ∨ (*ψ* ∨ *χ*)⊢(*φ* ∨ *ψ*)∨*χ*

```idris
orAssocRight : Either a (Either b c) -> Either (Either a b) c
orAssocRight = either (Left . Left) (first Right)
```
#### Formulation 1

(*φ* ∨ *ψ*)∨*χ* ⊣ ⊢*φ* ∨ (*ψ* ∨ *χ*)

#### Formulation 2

⊢((*φ* ∨ *ψ*)∨*χ*)⇔(*φ* ∨ (*ψ* ∨ *χ*))

#### Source

```idris
orAssoc : Either (Either a b) c <-> Either a (Either b c)
orAssoc = Conj orAssocLeft orAssocRight
```
### iffAnd

*φ* ⇔ *ψ* ⊢ (*φ* ⟹ *ψ*)∧(*ψ* ⟹ *φ*)

```idris
iffAnd : (a <-> b) -> (a -> b, b -> a)
iffAnd = id
```
### iffAndTo

*φ* ⇔ *ψ* ⊣ ⊢(*φ* ⟹ *ψ*)∧(*ψ* ⟹ *φ*)

or

⊢(*φ* ⇔ *ψ*)⇔((*φ* ⟹ *ψ*)∧(*ψ* ⟹ *φ*))

```idris
iffToAnd : (a <-> b) <-> (a -> b, b -> a)
iffToAnd = Conj id id
```

