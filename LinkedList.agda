{-

This file is a(n almost) one-to-one translation of the following blog post:
http://siek.blogspot.com/2024/06/data-structures-and-algorithms-correctly.html

Goals:

1) To see how easily can one translate proofs in Deduce to Agda.

2) For the more complicated proofs, figure out if adding gradual types help.

3) Deduce can only define non-dependent inductive types, so need to figure out if
  the same proofs can be done (easily?) using dependent inductive types.

4) If proving the same properties using dependent inductive types is tough, then
  would gradual typing help?

5) Figure out why just using holes doesn't suffice.

-}

module LinkedList where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; s<s)
open import Data.Nat.Properties using (+-suc)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_×_; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec)

{-
union List<T> {
  empty
  node(T, List<T>)
}
-}
data List (T : Set) : Set where
  empty : List T
  node  : T -> List T -> List T

{-
define list_123 : List<Nat> = node(1, node(2, node(3, empty)))
-}
list123 : List ℕ
list123 = node 1 (node 2 (node 3 empty))

{-
function length<E>(List<E>) -> Nat {
  length(empty) = 0
  length(node(n, next)) = 1 + length(next)
}
-}
length : {E : Set} -> List E -> ℕ
length empty = 0
length (node n next) = 1 + length next

{-
assert length(list_123) = 3
-}
testLength0 : length list123 ≡ 3
testLength0 = refl

{-
function nth<T>(List<T>, T) -> (fn Nat -> T) {
  nth(empty, default) = λi{default}
  nth(node(x, xs), default) = λi{
    if i = 0 then
      x
    else
      nth(xs, default)(pred(i))
  }
}
-}
nth : {T : Set} -> List T -> T -> ℕ -> T
nth empty default _ = default
nth (node x xs) default zero = x
nth (node x xs) default (suc i) = nth xs default i

{-
assert nth(list_123, 0)(0) = 1
assert nth(list_123, 0)(1) = 2
assert nth(list_123, 0)(2) = 3
assert nth(list_123, 0)(3) = 0
-}
testNth0 : nth list123 0 0 ≡ 1
testNth0 = refl
testNth1 : nth list123 0 1 ≡ 2
testNth1 = refl
testNth2 : nth list123 0 2 ≡ 3
testNth2 = refl
testNth3 : nth list123 0 3 ≡ 0
testNth3 = refl

{-
function interval(Nat, Nat) -> List<Nat> {
  interval(0, n) = empty
  interval(suc(k), n) = node(n, interval(k, suc(n)))
}
-}
interval : ℕ -> ℕ -> List ℕ
interval zero n = empty
interval (suc k) n = node n (interval k (suc n))

{-
assert interval(3, 5) = node(5, node(6, node(7, empty)))

assert length(interval(0, 0)) = 0

assert length(interval(1, 0)) = 1
assert nth(interval(1, 0), 7)(0) = 0 + 0

assert length(interval(2, 0)) = 2
assert nth(interval(2, 0), 7)(0) = 0 + 0
assert nth(interval(2, 0), 7)(1) = 1 + 0

assert length(interval(0, 3)) = 0

assert length(interval(1, 3)) = 1
assert nth(interval(1, 3), 7)(0) = 0 + 3

assert length(interval(2, 3)) = 2
assert nth(interval(2, 3), 7)(0) = 0 + 3
assert nth(interval(2, 3), 7)(1) = 1 + 3
-}
testInterval0 : interval 3 5 ≡ node 5 (node 6 (node 7 empty))
testInterval0 = refl

testInterval1 : length (interval 0 0) ≡ 0
testInterval1 = refl

testInterval2 : length (interval 1 0) ≡ 1
testInterval2 = refl
testInterval3 : nth (interval 1 0) 7 0 ≡ 0 + 0
testInterval3 = refl

testInterval4 : length (interval 2 0) ≡ 2
testInterval4 = refl
testInterval5 : nth (interval 2 0) 7 0 ≡ 0 + 0
testInterval5 = refl
testInterval6 : nth (interval 2 0) 7 1 ≡ 1 + 0
testInterval6 = refl

testInterval7 : length (interval 0 3) ≡ 0
testInterval7 = refl

testInterval8 : length (interval 1 3) ≡ 1
testInterval8 = refl
testInterval9 : nth (interval 1 3) 7 0 ≡ 0 + 3
testInterval9 = refl

testInterval10 : length (interval 2 3) ≡ 2
testInterval10 = refl
testInterval11 : nth (interval 2 3) 7 0 ≡ 0 + 3
testInterval11 = refl
testInterval12 : nth (interval 2 3) 7 1 ≡ 1 + 3
testInterval12 = refl

{-
theorem interval_length:
  all count:Nat. all start:Nat. length(interval(count, start)) = count
proof
  induction Nat
  case 0 {
    arbitrary start:Nat
    conclude length(interval(0, start)) = 0
        by definition {interval, length}
  }
  case suc(count')
    suppose IH: all start:Nat. length(interval(count', start)) = count'
  {
    arbitrary start:Nat
    suffices 1 + length(interval(count', suc(start))) = suc(count')
        with definition {interval, length}
    rewrite suc_one_add[count'] | IH[suc(start)]
  }
end
-}
intervalLength : (count : ℕ) (start : ℕ) -> length (interval count start) ≡ count
intervalLength zero start = refl
intervalLength (suc count') start = begin
                                   (length (interval (suc count') start))
                                   ≡⟨⟩
                                   (1 + (length (interval count' (suc start))))
                                   ≡⟨ cong suc (IH (suc start))⟩
                                   suc count' ∎
                                   where
                                     IH : ∀ (start : ℕ) -> length (interval count' start) ≡ count'
                                     IH = intervalLength count'

{-
theorem interval_nth: all count:Nat. all start:Nat, d:Nat, i:Nat.
  if i < count
  then nth(interval(count, start), d)(i) = i + start
proof
  induction Nat
  case 0 {
    arbitrary start:Nat, d:Nat, i:Nat
    suppose i_l_z: i < 0
    suffices d = i + start  with definition {interval, nth}
    conclude false by definition {operator <, operator ≤} in i_l_z
  }
  case suc(count')
    suppose IH: all start:Nat, d:Nat, i:Nat.
        if i < count' then nth(interval(count',start),d)(i) = i + start
  {
    arbitrary start:Nat, d:Nat, i:Nat
    suppose i_l_sc: i < suc(count')
    suffices nth(node(start, interval(count', suc(start))), d)(i) = i + start
        with definition interval
    switch i for nth {
      case 0 {
        conclude start = 0 + start  by definition operator +
      }
      case suc(i') suppose i_sc: i = suc(i') {
        suffices nth(interval(count',suc(start)),d)(i') = suc(i') + start
            with definition {pred}
        have i_l_cnt: i' < count'  by enable {operator <, operator ≤}
                                      rewrite i_sc in i_l_sc
        equations
          nth(interval(count',suc(start)),d)(i')
              = i' + suc(start)    by apply IH[suc(start), d, i'] to i_l_cnt
          ... = suc(i' + start)    by add_suc[i'][start]
          ... = suc(i') + start    by definition operator +
      }
    }
  }
end
-}
intervalNth : (count start d i : ℕ) -> i < count -> nth (interval count start) d i ≡ i + start
intervalNth (suc count') start d zero i<sc = refl
intervalNth (suc count') start d (suc i') (s<s i<cnt) =
  begin
  (nth (interval count' (suc start)) d i')
  ≡⟨ IH (suc start) d i' i<cnt ⟩
  i' + suc start
  ≡⟨ +-suc i' start ⟩
  suc (i' + start) ∎
  where
    IH : ∀ (start d i : ℕ) -> i < count' -> nth (interval count' start) d i ≡ i + start
    IH = intervalNth count'


{-
function append<E>(List<E>, List<E>) -> List<E> {
  FILL IN HERE
}
-}
append : {E : Set} -> List E -> List E -> List E
append empty rs = rs
append (node n ls) rs = node n (append ls rs)

{-
function all_elements<T>(List<T>, fn (T) -> bool) -> bool {
  all_elements(empty, P) = true
  all_elements(node(x, xs'), P) = P(x) and all_elements(xs', P)
}
-}
allElements : {T : Set} -> List T -> (T -> Bool) -> Bool
allElements empty P = true
allElements (node x xs') P = P x ∧ allElements xs' P

{-
define list_45 : List<Nat> = node(4, node(5, empty))
define list_1_5 = append(list_123, list_45)
assert all_elements(interval(3, 0),
                    λi{ nth(list_1_5, 0)(i) = nth(list_123,0)(i) })
assert all_elements(interval(2, 0),
                    λi{ nth(list_1_5, 0)(3 + i) = nth(list_45,0)(i) })

define num_elts = 20
define first_elts = 12
define second_elts = 8
define first_list = interval(first_elts,1)
define second_list = interval(second_elts, first_elts + 1)
define output_list = append(first_list, second_list)
assert all_elements(interval(first_elts, 0),
          λi{ nth(output_list, 0)(i) = nth(first_list,0)(i) })
assert all_elements(interval(second_elts, 0),
          λi{ nth(output_list, 0)(first_elts + i) = nth(second_list,0)(i) })
-}
list45 : List ℕ
list45 = node 4 (node 5 empty)
list1-5 : List ℕ
list1-5 = append list123 list45

{-
theorem nth_append_front:
  all T:type. all xs:List<T>. all ys:List<T>, i:Nat, d:T.
  if i < length(xs)
  then nth(append(xs, ys), d)(i) = nth(xs, d)(i)
proof
  FILL IN HERE
end
-}
nthAppendFront : (T : Set) (xs ys : List T) (i : ℕ) (d : T) -> i < length xs ->
  nth (append xs ys) d i ≡ nth xs d i
nthAppendFront T (node x xs) ys zero d _ = refl
nthAppendFront T (node x xs) ys (suc i) d (s<s i<|xs|) = IH i<|xs|
  where
    IH = nthAppendFront T xs ys i d

{-
theorem nth_append_back:
  all T:type. all xs:List<T>. all ys:List<T>, i:Nat, d:T.
  nth(append(xs, ys), d)(length(xs) + i) = nth(ys, d)(i)
proof
  FILL IN HERE
end
-}
nthAppendBack : (T : Set) (xs ys : List T) (i : ℕ) (d : T) ->
  nth (append xs ys) d (length xs + i) ≡ nth ys d i
nthAppendBack T empty ys i d = refl
nthAppendBack T (node x xs) ys i d = nthAppendBack T xs ys i d

{-

  This marks the end of all the functions covered in the block post. Let's
  evaluate how we fare in terms of our original goal mentioned above:

  1) Translating deduce proofs to Agda was pretty easy. The Agda proofs are
     shorter, but that's expected since Deduce is meant to be a teaching tool
     where proofs are supposed to be similar to pen-and-paper proofs and hence
     more prosaic.

  2) Since translating proofs was pretty easy, I don't see how gradual typing
     helps. However, it should be noted that for non-dependently typed data
     structures the invariants about them should be proved separately as a
     theorem or assumed for correctness criteria of functions which use these
     functions. In the case of lists the invariant is the fact that you can
     access only valid indices less than the length of the list to access
     elements. Since the data structure doesn't carry much proof content it's
     easier to ignore the correctness proofs in a gradual setting. I feel like
     it won't be the same when doing this whole exercise with dependent vectors.

  Before I address the other goals by proving correctness critera using vectors,
  I need to address a problem with the nth function and resolve it using the
  maybe type.

-}

-- Here is the logical definition of when an element is contained in a list
_∈_ : {T : Set} -> T -> List T -> Set
t ∈ empty = ⊥
t ∈ node e es = t ≡ e ⊎ (t ∈ es)

_<->_ : (A B : Set) -> Set
A <-> B = (A → B) × (B → A)

-- One would expect that nth is equivalent to ∈ in some way, but that isn't true
nth↮∈ : (T : Set) (ls : List T) (t d : T) -> ¬ ((∃[ n ] nth ls d n ≡ t) <-> (t ∈ ls))
nth↮∈ T ls t d ⟨ fst , snd ⟩ = {!!}

DecEq : Set -> Set
DecEq T = (a b : T) -> (a ≡ b) ⊎ ¬ (a ≡ b)

-- a lemma about ∈
∈Decidable : {T : Set} (t : T) (xs : List T) -> DecEq T -> t ∈ xs ⊎ ¬(t ∈ xs)
∈Decidable {T} t empty H = inj₂ λ x → x
∈Decidable {T} t (node x xs') H with ∈Decidable t xs' H
... | inj₁ t∈xs' = inj₁ (inj₂  t∈xs')
... | inj₂ not-t∈xs' with H t x
... | inj₁ t=x = inj₁ (inj₁ t=x)
... | inj₂ t≠x = inj₂ λ { (inj₁ x) → t≠x x ; (inj₂ y) → not-t∈xs' y }

lemma∈Dec : {T : Set} (t x : T) (xs : List T) -> t ∈ node x xs ⊎ ¬(t ∈ node x xs) -> t ∈ xs ⊎ ¬(t ∈ xs)
lemma∈Dec t x xs (inj₁ x₁) = {!!}
lemma∈Dec t x xs (inj₂ y) = {!!}


-- This theorem demonstrates that in both cases when the default value is in the
-- list or isn't, we can show that nth evaluates to the default value.
nthAmbig : (T : Set) (xs : List T) (d : T) (n : ℕ) -> d ∈ xs ⊎ ¬(d ∈ xs) -> nth xs d n ≡ d
-- ¬ (∃ n. nth xs d n ≡ d <-> d ∈ xs)
nthAmbig T (node x xs') d zero (inj₁ (inj₁ H)) = sym H
nthAmbig T (node x xs') d (suc n) ∈Dec@(inj₁ (inj₁ H)) = {!nthAmbig T xs' d n!}
nthAmbig T (node x xs') d n (inj₁ (inj₂ H)) = {!!}
nthAmbig T xs d n (inj₂ H) = {!!}

