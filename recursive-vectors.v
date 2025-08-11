Require Import PeanoNat.

Fixpoint Vecμ (A : Type) (n : nat) : Type :=
  match n with
  | O => unit
  | S n' => A * (Vecμ A n')
  end.

Print prod.

Fixpoint appendμ (A : Type) (m n : nat) (v1 : Vecμ A m) (v2 : Vecμ A n)
  : Vecμ A (m + n) :=
  match m as m'
        return forall (n : nat) (v1 : Vecμ A m') (v2 : Vecμ A n), Vecμ A (m' + n)
  with
  | O => fun (n : nat) (v1 : Vecμ A O) (v2 : Vecμ A n) =>
          v2
  | S m' => fun (n : nat) (v1 : Vecμ A (S m')) (v2 : Vecμ A n) =>
             match v1 return Vecμ A (S m' + n) with
             | pair hd tl => pair hd (appendμ A m' n tl v2)
             end
  end n v1 v2.
