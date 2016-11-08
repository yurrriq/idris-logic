---
pandoc-minted:
  language: idris
---

= Logic

> module Logic
>
> import Data.Bifunctor
>
> %default total
>
> %access export

== Iff

The following `iff`-related functions are ported from
[`Coq.Init.Logic`](https://coq.inria.fr/library/Coq.Init.Logic.html).

`iff a b`, written `a <-> b`, expresses the equivalence of `a` and `b`.

> infixl 9 <->
>
> public export
> (<->) : Type -> Type -> Type
> (<->) a b = (a -> b, b -> a)

$A \leftrightarrow A$

> iff_refl : a <-> a
> iff_refl = (id, id)

$(A \leftrightarrow B) \rightarrow (B \leftrightarrow C) \rightarrow (A \leftrightarrow C)$

> iff_trans : (a <-> b) -> (b <-> c) -> (a <-> c)
> iff_trans (ab, ba) (bc, cb) = (bc . ab, ba . cb)

$(A \leftrightarrow B) \rightarrow (B \leftrightarrow A)$

> iff_sym : (a <-> b) -> (b <-> a)
> iff_sym = swap

Since $(A \land B) \rightarrow B$ and $(A \land C) \rightarrow C$,
$(B \leftrightarrow C) \rightarrow ((A \land B) \leftrightarrow (A \land C))$.

> and_iff_compat_l : (b <-> c) -> ((a, b) <-> (a, c))
> and_iff_compat_l = bimap second second

Since $(B \land A) \rightarrow B$ and $(C \land A) \rightarrow C$,
$(B \leftrightarrow C) \rightarrow ((B \land A) \leftrightarrow (C \land A))$.

> and_iff_compat_r : (b <-> c) -> ((b, a) <-> (c, a))
> and_iff_compat_r = bimap first first

Since $B \rightarrow (A \lor B)$ and $C \rightarrow (A \lor C)$,
$(B \leftrightarrow C) \rightarrow ((A \lor B) \leftrightarrow (A \lor C))$.

> or_iff_compat_l : (b <-> c) -> (Either a b <-> Either a c)
> or_iff_compat_l = bimap second second

Since $B \rightarrow (B \lor A)$ and $C \rightarrow (C \lor A)$,
$(B \leftrightarrow C) \rightarrow ((B \lor A) \leftrightarrow (C \lor A))$.

> or_iff_compat_r : (b <-> c) -> (Either b a <-> Either c a)
> or_iff_compat_r = bimap first first

$\neg A \leftrightarrow (A \leftrightarrow \bot)$

> neg_void : Not a <-> (a <-> Void)
> neg_void = (flip MkPair void, fst)

Given $B \rightarrow A$ and $C \rightarrow A$,
$((A \land B) \leftrightarrow (A \land C)) \leftrightarrow (B \leftrightarrow C)$.

> and_cancel_l : (b -> a) -> (c -> a) -> (((a, b) <-> (a, c)) <-> (b <-> c))
> and_cancel_l ba ca = (bimap f g, and_iff_compat_l)
>   where
>     f pf b = snd $ pf (ba b, b)
>     g pg c = snd $ pg (ca c, c)

Given $B \rightarrow A$ and $C \rightarrow A$,
$((B \land A) \leftrightarrow (C \land A)) \leftrightarrow (B \leftrightarrow C)$.

> and_cancel_r : (b -> a) -> (c -> a) -> (((b, a) <-> (c, a)) <-> (b <-> c))
> and_cancel_r ba ca = (bimap f g, and_iff_compat_r)
>   where
>     f pf b = fst $ pf (b, ba b)
>     g pg c = fst $ pg (c, ca c)

$(A \land B) \leftrightarrow (B \land A)$

> and_comm : (a, b) <-> (b, a)
> and_comm = (swap, swap)

$((A \land B) \land C) \leftrightarrow (A \land B \land C)$

> and_assoc : ((a, b), c) <-> (a, b, c)
> and_assoc = (\((a, b), c) => (a, b, c), \(a, b, c) => ((a, b), c))

$(B \rightarrow \neg A) \rightarrow (C \rightarrow \neg A) \rightarrow (((A \lor B) \leftrightarrow (A \lor C)) \leftrightarrow (B \leftrightarrow C))$

> or_cancel_l : (b -> Not a)
>            -> (c -> Not a)
>            -> ((Either a b <-> Either a c) <-> (b <-> c))
> or_cancel_l bNotA cNotA = (bimap f g, or_iff_compat_l)
>   where
>     f ef b = go (bNotA b) (ef (Right b))
>     g eg c = go (cNotA c) (eg (Right c))
>     go : Not a -> Either a b -> b
>     go lf = either (void . lf) id

$(B \rightarrow \neg A) \rightarrow (C \rightarrow \neg A) \rightarrow (((B \lor A) \leftrightarrow (C \lor A)) \leftrightarrow (B \leftrightarrow C))$

> or_cancel_r : (b -> Not a)
>            -> (c -> Not a)
>            -> ((Either b a <-> Either c a) <-> (b <-> c))
> or_cancel_r bNotA cNotA = (bimap f g, or_iff_compat_r)
>   where
>     f ef b = go (bNotA b) (ef (Left b))
>     g eg c = go (cNotA c) (eg (Left c))
>     go : Not p -> Either q p -> q
>     go rf = either id (void . rf)

$(A \lor B) \leftrightarrow (B \lor A)$

> or_comm : Either a b <-> Either b a
> or_comm = (mirror, mirror)

$((A \lor B) \lor C) \rightarrow (A \lor (B \lor C))$

> or_assoc_lemma1 : Either (Either a b) c -> Either a (Either b c)
> or_assoc_lemma1 = either (second Left) (pure . pure)

$(A \lor (B \lor C)) \rightarrow ((A \lor B) \lor C)$

> or_assoc_lemma2 : Either a (Either b c) -> Either (Either a b) c
> or_assoc_lemma2 = either (Left . Left) (first Right)

$((A \lor B) \lor C) \leftrightarrow (A \lor (B \lor C))$

> or_assoc : Either (Either a b) c <-> Either a (Either b c)
> or_assoc = (or_assoc_lemma1, or_assoc_lemma2)

$(A \leftrightarrow B) \rightarrow ((A \rightarrow B) \land (B \rightarrow A))$

> iff_and : (a <-> b) -> (a -> b, b -> a)
> iff_and = id

$(A \leftrightarrow B) \leftrightarrow ((A \rightarrow B) \land (B \rightarrow A))$

> iff_to_and : (a <-> b) <-> (a -> b, b -> a)
> iff_to_and = (id, id)
