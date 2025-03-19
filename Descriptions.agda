module Descriptions where

open import Data.Product.Base using (_×_ ; Σ-syntax ; _,_)
open import Data.Unit using (⊤ ; tt)
open import Data.Bool using (true ; false ; if_then_else_) renaming (Bool to 𝔹)
open import Agda.Primitive using (Level)

data Desc : Set₁ where
  End : Desc
  Arg : (A : Set) → (A → Desc) → Desc
  Rec : (A : Set) → Desc → Desc

El : Desc → Set → Set
El End X = ⊤
El (Arg A D) X = Σ[ a ∈ A ] El (D a) X
El (Rec A D) X = (A → X) × (El D X)

data μ (D : Desc) : Set where
  init : El D (μ D) → μ D

--TODO: Define booleans using a descriptor

ℕ : Set
ℕ = μ(Arg 𝔹 (λ b → if b then End else (Rec ⊤ End)))

Z : ℕ
Z = init (true , tt)

S : ℕ → ℕ
S n = init (false , (λ _ → n) , tt)

three : ℕ
three = S (S (S Z))

indℕ : {ℓ : Level} (P : ℕ → Set ℓ) → (P Z) → ((n : ℕ) → (P n) → P(S n)) → (x : ℕ) → P x
indℕ P Pz PSn (init (true , tt)) = Pz
indℕ P Pz PSn (init (false , ⊤→ℕ , tt)) = PSn (⊤→ℕ tt) (indℕ P Pz PSn (⊤→ℕ tt))

recℕ : {A : Set} → (ℕ → A → A) → A → ℕ → A
recℕ {A} f acc n = indℕ (λ _ → A) acc f n

infixl 20 _+_

_+_ : ℕ → ℕ → ℕ
--init (true , tt) + n = n
--init (false , tt→m , tt) + n = S (tt→m tt + n)
m + n = recℕ (λ m′ acc′ → S acc′) n m

ten : ℕ
ten = three + three + three + S Z

List : Set → Set
List A = μ(Arg 𝔹 (λ b → if b then End else (Arg A (λ x → Rec ⊤ End))))

[] : { A : Set } → List A
[] = init (true , tt)

infixr 4 _∷_

_∷_ : { A : Set } → A → List A → List A
h ∷ t = init (false , (h , (λ _ → t) , tt))

list3 : List ℕ
list3 = three ∷ S (S Z) ∷ S Z ∷ []

indList : {ℓ : Level} (A : Set) → (P : List A → Set ℓ )
          → (P [])
          → ((h : A) → (t : List A) → (P t) → P(h ∷ t))
          → (l : List A) → P l
indList A P P[] P∷ (init (true , tt)) = P[]
indList A P P[] P∷ (init (false , head , tt→tail , tt)) = P∷ head (tt→tail tt) (indList A P P[] P∷ (tt→tail tt))

recList : {A B : Set} → (A → List A → B → B) → B → List A → B
recList {A} {B} f acc l = indList A (λ _ → B) acc f l

sum : List ℕ → ℕ
sum l = recList (λ h t acc → h + acc) Z l

sumList3 : ℕ
sumList3 = sum list3

-- TODO: Define Vector types using indexed version of Desc
