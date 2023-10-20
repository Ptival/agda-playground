module DigitList where

open import Data.Bool hiding (_<?_; _≤?_; _<_)
open import Data.Fin hiding (_+_ ; _<?_; _≤?_; _<_)
open import Data.Fin.Properties using (toℕ-inject₁)
open import Data.List
open import Data.Nat hiding (pred)
open import Data.Nat.Properties
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

Digits : ℕ → Set
Digits b = List (Fin b)

Dsucc-overflows : (b : ℕ) → .{{NonZero b}} → Digits b → (Bool × Digits b)
Dsucc-overflows _ [] = ( true , [] )
Dsucc-overflows b@(suc _) (d ∷ ds) with Dsucc-overflows b ds
...                                | (true , sds) with toℕ d + 1 <? b
...                                               | yes y = (false , # (toℕ d + 1) ∷ sds)
...                                               | no n = (true , # 0 ∷ sds)
Dsucc-overflows _ (d ∷ ds)         | (false , sds) = (false , d ∷ sds)

Dsucc : {b : ℕ} → .{{NonZero b}} → Digits b → Digits b
Dsucc {suc zero} ds = # 0 ∷ ds
Dsucc {suc (suc _)} d with Dsucc-overflows _ d
... | (true , sds) = # 1 ∷ sds
... | (false , sds) = sds

-- AKA multiply by `b`
shiftL : {b : ℕ} → .{{NonZero b}} → Digits b → Digits b
shiftL {suc _} [] = [ # 0 ]
-- shiftL (d ∷ []) = d ∷ [ # 0 ]
shiftL (d ∷ ds) = d ∷ shiftL ds

bag : {b : ℕ} → .{{NonZero b}} → Digits b → Digits b
bag {suc zero} ds = # 0 ∷ ds -- in base 1, things are quite degenerate
bag {suc (suc _)} [] = [ #_ 1 ]
bag {suc (suc _)} (zero ∷ ds) = bag ds
bag b@{suc (suc _)} (d ∷ ds) with toℕ d + 1 <? b
... | yes y = # (toℕ d + 1) ∷ ds -- TODO: convince Agda
... | no n = # 1 ∷ shiftL ds

Dtoℕ : {b : ℕ} → Digits b → ℕ
Dtoℕ [] = 0
Dtoℕ (d ∷ []) = toℕ d
Dtoℕ {b} (d ∷ ds) = toℕ d * b ^ (length ds) + Dtoℕ ds

predBase : (b : ℕ) → .{{NonZero b}} → ℕ
predBase (suc b) = b

-- (d + 1) × b^n + rest ≡ b^n + (d * b^n) + rest
Dtoℕ-suc :
  {b↓ : ℕ} → (d : Fin b↓) → (ds : Digits (suc b↓)) →
  Dtoℕ {suc b↓} (suc d ∷ ds) ≡ suc b↓ ^ length ds + Dtoℕ {suc b↓} (inject₁ d ∷ ds)
Dtoℕ-suc d [] = cong suc (sym (toℕ-inject₁ _))
Dtoℕ-suc {b↓} d ds@(_ ∷ _) =
  begin
    Dtoℕ {suc b↓} (suc d ∷ ds)
    ≡⟨ refl ⟩
    toℕ (suc d) * (suc b↓ ^ length ds) + Dtoℕ ds
    ≡⟨ refl ⟩
    (1 + (toℕ d)) * (suc b↓ ^ length ds) + Dtoℕ ds
    ≡⟨ refl ⟩
    suc b↓ ^ length ds + toℕ d * (suc b↓ ^ length ds) + Dtoℕ ds
    -- Why do I need to help the unifier so much!? :'(
    ≡⟨  (+-assoc (suc b↓ ^ length ds) (toℕ d * (suc b↓ ^ length ds)) (Dtoℕ ds)) ⟩
    suc b↓ ^ length ds + (toℕ d * (suc b↓ ^ length ds) + Dtoℕ ds)
    -- Why do I need to help the unifier so much!? :'(
    ≡⟨ cong₂ _+_ {suc b↓ ^ length ds} refl (cong₂ _+_ (cong₂ _*_ (sym (toℕ-inject₁ d)) refl) refl) ⟩
    suc b↓ ^ length ds + (toℕ (inject₁ d) * (suc b↓ ^ length ds) + Dtoℕ ds)
    ≡⟨ refl ⟩
    suc b↓ ^ length ds + Dtoℕ {suc b↓} (inject₁ d ∷ ds)
  ∎
  where open ≡-Reasoning

thirteen : Digits 3
thirteen = # 1 ∷ # 1 ∷ # 1 ∷ []

check-13 = Dtoℕ thirteen
check-bag-13 = Dtoℕ (bag thirteen)

two : Digits 3
two = [ # 2 ]

check-bag-2 = Dtoℕ (bag two)

zeroFin : {b : ℕ} → .{{NonZero b}} → Fin b
zeroFin {suc b↓} = zero {b↓}

Dtoℕ-leading-0 : {b : ℕ} → .{{_ : NonZero b}} → (ds : Digits b) → Dtoℕ {b} (zeroFin ∷ ds) ≡ Dtoℕ ds
Dtoℕ-leading-0 {suc _} [] = refl
Dtoℕ-leading-0 {suc _} (x ∷ ds) = refl

-- I feel like there's gotta be a helper for this...
<-Dtoℕ-leading-0s : {ms ns : Digits 3} → Dtoℕ (zero ∷ ms) < Dtoℕ (zero ∷ ns) → Dtoℕ ms < Dtoℕ ns
<-Dtoℕ-leading-0s {ms} {ns} zms<zns =
  begin
  suc (Dtoℕ ms)
  ≡⟨ cong suc (sym (Dtoℕ-leading-0 ms)) ⟩
  suc (Dtoℕ (zero ∷ ms))
  ≤⟨ zms<zns ⟩
  Dtoℕ (zero ∷ ns)
  ≡⟨ Dtoℕ-leading-0 ns ⟩
  Dtoℕ ns
  ∎
  where open ≤-Reasoning

mono-3 : (m n : Digits 3) → Dtoℕ m < Dtoℕ n → Dtoℕ (bag m) < Dtoℕ (bag n)
-- This may be much easier without doing much pattern-match on n?
mono-3 [] (zero ∷ ns) m<n = mono-3 [] ns (<-≤-trans m<n (≤-reflexive (Dtoℕ-leading-0 ns)))
mono-3 [] (suc n ∷ ns) m<n with toℕ (suc n) + 1 <? 3
... | yes y = {!   !}
... | no n = {!   !}

mono-3 (zero ∷ ms) (zero ∷ ns) m<n =
  begin
    suc (Dtoℕ (bag ms))
    ≡⟨ cong suc (sym (Dtoℕ-leading-0 (bag ms))) ⟩
    suc (Dtoℕ (zero ∷ bag ms))
    ≤⟨ {! mono-3 !} ⟩
    Dtoℕ (zero ∷ bag ns)
    ≡⟨ Dtoℕ-leading-0 (bag ns) ⟩
    Dtoℕ (bag ns)
  ∎
  where open ≤-Reasoning

mono-3 (zero ∷ ms) (suc n ∷ ns) m<n = {!   !}
mono-3 (suc m ∷ ms) (zero ∷ ns) m<n = {!   !}
mono-3 (suc m ∷ ms) (suc n ∷ ns) m<n = {!   !}
  -- begin
  --   {!   !}
  --   <⟨ {!   !} ⟩ {!   !}
  -- ∎
--   where open ≤-Reasoning
