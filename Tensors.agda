module Tensors where

open import Data.List using (List; []; _∷_; length; product; _++_)
open import Data.Vec using (Vec) renaming ([] to <>; _∷_ to _∺_; map to vmap)
open import Data.Float using (Float; _+_)
open import Data.Nat using (ℕ; suc; zero; _<ᵇ_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Relation.Nullary.Negation using (¬_)
open import Data.Product.Base using (∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

data Tensor : List ℕ -> Set where
  scalar : Float -> Tensor []
  tensor : {n : ℕ} {s : List ℕ} -> Vec (Tensor s) (suc n) -> Tensor (suc n ∷ s)

t0-r2 : Tensor (3 ∷ 2 ∷ [])
t0-r2 = tensor (tensor ((scalar 1.0) ∺ ((scalar 2.0) ∺ <>)) ∺
                tensor ((scalar 3.0) ∺ ((scalar 4.0) ∺ <>)) ∺
                tensor ((scalar 5.0) ∺ ((scalar 6.0) ∺ <>)) ∺
                <>)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

--tbad : Tensor (2 ∷ 0 ∷ [])
--tbad = tensor ({!!} ∺ ({!!} ∺ <>))

-- Shape of a tensor cannot contain a zero
0∉shape : (s : List ℕ) (t : Tensor s) -> 0 ∉ s
0∉shape .(suc n ∷ s') (tensor {n} {s'} (t ∺ v)) (there x) = IH x
  where
    IH : 0 ∉ s'
    IH = 0∉shape s' t

Shape = ∃[ s ] 0 ∉ s

shape : {s : List ℕ} -> Tensor s -> Shape
proj₁ (shape {s = s} _) = s
proj₂ (shape {s = s} t) = 0∉shape s t

rank : {s : List ℕ} -> Tensor s -> ℕ
rank {s = s} _ = length s

tensor¹ : {n : ℕ} -> Vec Float (suc n) -> Tensor (suc n ∷ [])
tensor¹ v = tensor (vmap scalar v)

t0-r3 = tensor (tensor (tensor¹ ( 1.0 ∺  2.0 ∺  3.0 ∺  4.0 ∺ <>) ∺
                        tensor¹ ( 5.0 ∺  6.0 ∺  7.0 ∺  8.0 ∺ <>) ∺ <>) ∺
                tensor (tensor¹ ( 9.0 ∺ 10.0 ∺ 11.0 ∺ 12.0 ∺ <>) ∺
                        tensor¹ (13.0 ∺ 14.0 ∺ 15.0 ∺ 16.0 ∺ <>) ∺ <>) ∺
                tensor (tensor¹ (17.0 ∺ 18.0 ∺ 19.0 ∺ 20.0 ∺ <>) ∺
                        tensor¹ (21.0 ∺ 22.0 ∺ 23.0 ∺ 24.0 ∺ <>) ∺ <>) ∺ <>)

build-vector : {A : Set} -> (ℕ -> A) -> (n : ℕ) -> Vec A n
build-vector f zero = <>
build-vector f (suc n) = f n ∺ build-vector f n

build-tensor' : {s' : List ℕ} -> (s : Shape) -> (Vec ℕ (length (proj₁ s)) -> Tensor s') -> List ℕ -> Tensor (proj₁ s ++ s')
build-tensor' ⟨ [] , 0∉s ⟩ f a = f {!!}
build-tensor' ⟨ zero ∷ [] , 0∉[z] ⟩ f a with 0∉[z] (here {ℕ} {0 ≡_} {0} {[]} refl)
... | ()
build-tensor' ⟨ suc x ∷ [] , 0∉[sx] ⟩ f a = tensor (build-vector (λ i → {!!}) {!!})
build-tensor' ⟨ x ∷ y ∷ s , 0∉s ⟩ f a = {!!}

build-tensor : {s' : List ℕ} -> (s : Shape) -> (Vec ℕ (length (proj₁ s)) -> Tensor s') -> Tensor (proj₁ s ++ s')
build-tensor = {!!}

reshape : {s : List ℕ} -> Tensor s -> (r : List ℕ) -> product s ≡ product r -> Tensor r
reshape t r H = {!!}


