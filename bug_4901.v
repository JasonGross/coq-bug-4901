Require Import Coq.NArith.NArith Coq.Arith.Div2.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive word : nat -> Set :=
| WO : word O
| WS : bool -> forall n, word n -> word (S n).

Fixpoint mod2 (n : nat) : bool :=
  match n with
  | 0 => false
  | 1 => true
  | S (S n') => mod2 n'
  end.

Fixpoint wordToN sz (w : word sz) : N :=
  match w with
  | WO => 0
  | WS false _ w' => 2 * wordToN w'
  | WS true _ w' => Nsucc (2 * wordToN w')
  end%N.

Fixpoint natToWord (sz n : nat) : word sz :=
  match sz with
  | O => WO
  | S sz' => WS (mod2 n) (natToWord sz' (div2 n))
  end.

Definition bar (n n0 : nat)
           (_32 := 10)
           (_4 : nat) (P : Set) (w : forall _ : N, P)
  : @eq P (w (@wordToN _32 (natToWord _32 (n + n0)%nat))) (w (@wordToN _32 (natToWord _32 (n * _4)%nat))).
  Time Timeout 1 repeat esplit.
Abort.

Definition foo (n n0 : nat)
           (_32 := 32)
           (_4 : nat) (P : Set) (w : forall _ : N, P)
  : @eq P (w (@wordToN _32 (natToWord _32 (n + n0)%nat))) (w (@wordToN _32 (natToWord _32 (n * _4)%nat))).
  Time Timeout 1 repeat esplit.
Abort.

Definition baz (n n0 : nat)
           (_32 := 64)
           (_4 : nat) (P : Set) (w : forall _ : N, P)
  : @eq P (w (@wordToN _32 (natToWord _32 (n + n0)%nat))) (w (@wordToN _32 (natToWord _32 (n * _4)%nat))).
  Time Timeout 2 repeat esplit.
Abort.
