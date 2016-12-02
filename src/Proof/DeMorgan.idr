module Proof.DeMorgan

%access  public export
%default total

syntax "($" [x] ")" = \f => f x

infixl 8 .:
(.:) : (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(.:) = (.) . (.)

||| https://proofwiki.org/wiki/Rule_of_Addition/Proof_Rule#Proof_Rule
add1 : p -> Either p q
add1 = Left

add2 : q -> Either p q
add2 = Right

||| https://proofwiki.org/wiki/Double_Negation/Double_Negation_Introduction/Proof_Rule
doubleNegation : p -> Not (Not p)
doubleNegation = flip id

idempotenceAnd : p -> (p, p)
idempotenceAnd p = (p, p)

idempotenceAnd' : (p, p) -> p
idempotenceAnd' = fst

idempotenceOr : p -> Either p p
idempotenceOr = Right

idempotenceOr' : Either p p -> p
idempotenceOr' = fromEither

contrapositive : (p -> q) -> (Not q -> Not p)
contrapositive = flip (.)

notE : p -> Not p -> Void
notE = flip id

notE' : Not p -> p -> Void
notE' = flip notE

-- notE_and : (p, q) -> Not p -> Void
-- notE_and = notE . fst

||| https://proofwiki.org/wiki/Modus_Ponendo_Ponens/Proof_Rule
modusPonendoPonens : (p -> q) -> p -> q
modusPonendoPonens = id

modusTollendoPonens : (Either p q) -> Not p -> q
modusTollendoPonens = either (void .: notE) const

excludedMiddle : p -> Either p (Not p)
excludedMiddle = Left

excludedMiddle2 : Not (Not p -> q) -> Not (Either p q)
excludedMiddle2 = (. modusTollendoPonens)

||| https://proofwiki.org/wiki/Rule_of_Material_Implication/Formulation_1/Forward_Implication
materialImplication1F : p -> q -> Either (Not p) q
materialImplication1F p q = Right q

||| https://proofwiki.org/wiki/Rule_of_Material_Implication/Formulation_1/Reverse_Implication
materialImplication1R : Either (Not p) q -> p -> q
materialImplication1R = (. doubleNegation) . modusTollendoPonens

||| https://proofwiki.org/wiki/Implication_Equivalent_to_Negation_of_Conjunction_with_Negative/Formulation_1/Forward_Implication
implEquivNegConjWithNeg : (p -> q) -> Not (p, Not q)
implEquivNegConjWithNeg f (p, notQ) = notE (modusPonendoPonens f p) notQ


||| https://proofwiki.org/wiki/De_Morgan%27s_Laws_(Logic)/Conjunction_of_Negations/Formulation_1/Forward_Implication
deMorganConjNeg1F : (Not p, Not q) -> Not (Either p q)
deMorganConjNeg1F (f, g) = notE' (either f g)

||| https://proofwiki.org/wiki/De_Morgan%27s_Laws_(Logic)/Conjunction_of_Negations/Formulation_1/Reverse_Implication
deMorganConjNeg1R : Not (Either p q) -> (Not p, Not q)
deMorganConjNeg1R f = (notE' f . add1, notE' f . add2)
-- TODO: Arrows?

||| https://proofwiki.org/wiki/De_Morgan%27s_Laws_(Logic)/Disjunction_of_Negations/Formulation_1/Forward_Implication
deMorganDisjNeg1F : Either (Not p) (Not q) -> Not (p, q)
deMorganDisjNeg1F e (p, q) = either ($ p) ($ q) e

||| https://proofwiki.org/wiki/De_Morgan%27s_Laws_(Logic)/Disjunction_of_Negations/Formulation_1/Reverse_Implication
-- deMorganDisjNeg1R : Not (p, q) -> Either (Not p) (Not q)
-- deMorganDisjNeg1R x = ?deMorganDisjNeg1R_rhs

||| https://proofwiki.org/wiki/De_Morgan%27s_Laws_(Logic)/Conjunction_of_Negations/Formulation_2
deMorganConjNeg2F : (Not p, Not q) -> Not (Either p q)
deMorganConjNeg2F (notP, notQ)
  = either (deMorganDisjNeg1F (Left notP) . idempotenceAnd) notQ

deMorganConjNeg2R : Not (Either p q) -> (Not p, Not q)
deMorganConjNeg2R = deMorganConjNeg1R


-- https://gist.github.com/gallais/75100e26fc4be48eb3d31ae5ed6d1198

postulate LEM : (p : Type) -> Dec p

lemma : (a -> b -> c) -> (a -> b) -> c
lemma f g = let gg = const g in f ?lemma_rhs1 (g ?lemma_rhs2)

doubleNegation' : Not (Not p) -> p
doubleNegation' {p} notNotP
  = let x = contra
    in  ?doubleNegation'_rhs
  where
    contra : Not p -> p
    contra = void . notNotP


-- doubleNegation' {p} notNotP with (LEM p)
--   | Yes prf = prf
--   | No contra = ?rhs_rhs_2



-- = case LEM p of
--                              (Yes prf) => prf
--                              (No notP) => void $ notE notNotP notP
