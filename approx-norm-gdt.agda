import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Vec using (Vec; _∷_; [])

head : (A : Set) -> (n : ℕ) -> Vec A (n + 1) -> A
head A n x with subst (λ k -> Vec A k) (+-comm n 1) x
... | x ∷ _ = x

head' : (A : Set) -> (n m : ℕ) -> n ≡ m + 1 -> Vec A n -> A
head' A n m n≡m+1 x with subst (λ k -> Vec A k)
                               (begin n ≡⟨ n≡m+1 ⟩
                                      m + 1 ≡⟨ +-comm m 1 ⟩
                                      1 + m ≡⟨⟩
                                      suc m ∎)
                               x
... | x ∷ _ = x
