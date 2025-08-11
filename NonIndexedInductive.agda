module NonIndexedInductive where

open import Data.Vec using (Vec) renaming ([] to <>; _∷_ to _∺_; map to vmap)
open import Data.Nat using (ℕ; suc; zero; _+_; _<ᵇ_)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (∃-syntax; proj₁; proj₂; _×_; _,_)

isEqNat : ℕ → ℕ → Set
isEqNat zero zero = ⊤
isEqNat zero (suc n) = ⊥
isEqNat (suc m) zero = ⊥
isEqNat (suc m) (suc n) = isEqNat m n


data EqNat (m n : ℕ): Set where
  reflNat : isEqNat m n → EqNat m n

data EqNat' (m n : ℕ): Set where
  eqZero : isEqNat m 0 → isEqNat n 0 → EqNat' m n
  eqSuc : (m' n' : ℕ) → isEqNat m (suc m') → isEqNat n (suc n') → EqNat' m' n' → EqNat' m n

injEqNat : {m n : ℕ} → EqNat m n → EqNat (suc m) (suc n)
injEqNat {zero} {zero} (reflNat tt) = reflNat tt
injEqNat {suc m} {suc n} (reflNat x) = reflNat x

reflEqNat : {n : ℕ} → EqNat n n
reflEqNat {zero} = reflNat tt
reflEqNat {suc n} = injEqNat (reflEqNat {n})

symEqNat : {m n : ℕ} → EqNat m n → EqNat n m
symEqNat {zero} {zero} m=n = reflNat tt
symEqNat {zero} {suc n} (reflNat ())
symEqNat {suc m} {zero} (reflNat ())
symEqNat {suc m} {suc n} (reflNat m=?n) = injEqNat (symEqNat (reflNat m=?n))

transEqNat : {m n o : ℕ} → EqNat m n → EqNat n o → EqNat m o
transEqNat {zero} {zero} {o} m=n n=o = n=o
transEqNat {zero} {suc n} {o} (reflNat ()) n=o
transEqNat {suc m} {zero} {o} (reflNat ()) n=o
transEqNat {suc m} {suc n} {zero} m=n (reflNat ())
transEqNat {suc m} {suc n} {suc o} (reflNat m=?n) (reflNat n=?o) = injEqNat {m} {o}
  (transEqNat {m} {n} {o} (reflNat m=?n) (reflNat n=?o))

eqNatSubst : {m n : ℕ} (P : ℕ → Set) → EqNat m n → P m → P n
eqNatSubst {zero} {zero} P m=n pm = pm
eqNatSubst {zero} {suc n} P (reflNat ()) pm
eqNatSubst {suc m} {zero} P (reflNat ()) pm
eqNatSubst {suc m} {suc n} P (reflNat x) pSm = {!!}

data VecF (A : Set) (n : ℕ) : Set where
  nilF : EqNat 0 n → VecF A n
  consF : A → {m : ℕ} → (EqNat (suc m) n) → VecF A m → VecF A n

eqNatSubstVec : {m n : ℕ} {A : Set} → EqNat m n → VecF A m → VecF A n
eqNatSubstVec {zero} {zero} m=n pm = pm
eqNatSubstVec {zero} {suc n} (reflNat ()) pm
eqNatSubstVec {suc m} {zero} (reflNat ()) pm
eqNatSubstVec {suc m} {suc n} Sm=Sn (nilF (reflNat ()))
eqNatSubstVec {suc m} {suc n} {A} (reflNat m=?n) (consF a (reflNat m'=?m) vm')
  = consF a (reflNat m=?n) (eqNatSubstVec (reflNat m'=?m) vm')


subst-vec-f : (m n : ℕ) (A : Set) → EqNat m n → VecF A m → VecF A n
subst-vec-f zero zero A p v = {!!}
subst-vec-f zero (suc n) A p v = {!!}
subst-vec-f (suc m) zero A p v = {!!}
subst-vec-f (suc m) (suc n) A p v = {!!}

¬Sn=O : {n : ℕ} → EqNat (suc n) 0 → ⊥
¬Sn=O {zero} (reflNat x) = x
¬Sn=O {suc n} (reflNat x) = x

n=O+n : {n m : ℕ} → EqNat 0 m → EqNat n (m + n)
n=O+n {n} {zero} m=O = reflEqNat
n=O+n {n} {suc m} (reflNat ())

S|m+n|=Sm+n : {m n o : ℕ} → EqNat (suc m) o → EqNat (suc (m + n)) (o + n)
S|m+n|=Sm+n {o = zero} (reflNat ())
S|m+n|=Sm+n {zero} {n} {suc o} (reflNat O=?o) = injEqNat (n=O+n (reflNat O=?o))
S|m+n|=Sm+n {suc m} {n} {suc o} (reflNat Sm=?o) = injEqNat (S|m+n|=Sm+n {m} {n} {o} (reflNat Sm=?o))

vecFAppend : {A : Set} {m n : ℕ} → VecF A m → VecF A n → VecF A (m + n)
vecFAppend (nilF O=m) v2 = eqNatSubstVec (n=O+n O=m) v2
vecFAppend (consF a Sm=m₁ vm) v2 = consF a (S|m+n|=Sm+n Sm=m₁) (vecFAppend vm v2)

v1 : VecF ℕ 2
v1 = consF {n = 2} 1 (reflNat tt) (consF {n = 1} 2 (reflNat tt) (nilF {n = 0} (reflNat tt)))

v2 : VecF ℕ 2
v2 = consF {n = 2} 3 (reflNat tt) (consF {n = 1} 4 (reflNat tt) (nilF {n = 0} (reflNat tt)))

v3 : VecF ℕ 4
v3 = vecFAppend v1 v2

Vecμ : (A : Set) (n : ℕ) → Set
Vecμ A zero = ⊤
Vecμ A (suc n) = A × Vecμ A n

vecμAppend : {A : Set} {m n : ℕ} → Vecμ A m → Vecμ A n → Vecμ A (m + n)
vecμAppend {m = zero} v1 v2 = v2
vecμAppend {m = suc m} (a , v1') v2 = a , (vecμAppend v1' v2)

v1' : Vecμ ℕ 2
v1' = 1 , (2 , tt)

v2' : Vecμ ℕ 2
v2' = 3 , (4 , tt)

v3' : Vecμ ℕ 4
v3' = vecμAppend v1' v2'


--filter : ∀ {A n} → (A → Bool) → Vec A n → Vec A {!!}
--filter f <>       = <>
--filter f (a ∺ as) with (f a)
--... | true  = a ∺ filter f as
--... | false = filter f as
--
--filter-ex = filter (\ x -> x <ᵇ 2) (1 ∺ 2 ∺ 3 ∺ 4 ∺ <>)

vhead : ∀ {A n} → VecF A (suc n) → A
vhead (nilF (reflNat ()))
vhead (consF hd _ _) = hd

vlen :  ∀ {A n} → VecF A (suc n) → ℕ
vlen {n = n} _ = n
