Require Import Reals.
Open Scope R_scope.
Require Import Lra. (* Linear Reals Arith *)
Require Import Classical.
Require Import ZArith.
(* pierwszy podpunkt - definicja ciągu, zbieżności do granicy i zbieżności*)

Definition sequence := nat -> R.
Definition limit_g (s : sequence) (g : R) :=
  forall eps : R, eps > 0 -> exists N : nat, forall n : nat, (n >= N)%nat -> Rabs ((s n)-g) < eps.
Definition limit (s: sequence) := exists g : R , limit_g s g.

(* drugi podpunkt - dowód jednoznaczności wyznaczenia granicy *)
(*Lematy pomocnicze *)
Lemma not_eq_1: forall (a b: R), a <> b <-> exists eps : R, eps > 0 /\ Rabs (a - b) = eps.
Proof.
  intros a b.
  split.
  (* a <> b -> exists eps > 0, Rabs (a - b) = eps *)
  intros H.
  exists (Rabs (a - b)).
  split.
  apply Rabs_pos_lt.
  unfold not.
  intros.
  apply H.
  apply Rminus_diag_uniq.
  exact H0.
  reflexivity.
  (* (exists eps > 0, Rabs (a - b) = eps) -> a <> b *)
  intros [eps [H_eps H_eq]].
  unfold not.
  intros H_eq_ab.
  rewrite H_eq_ab in H_eq.
  rewrite Rminus_eq_0 in H_eq.
  rewrite Rabs_R0 in H_eq.
  lra.
Qed.

Lemma eq_implies_not_neq : forall (a b : R), a = b <-> (a <> b -> False).
Proof.
  intros.
  split.
  intros.
  unfold not in H0.
  rewrite H in H0.
  apply H0.
  reflexivity.
  intros.
  unfold not in H.
  apply NNPP in H.
  rewrite H.
  trivial.
Qed.
Lemma Rle_trans_lt : forall r1 r2 r3 : R, r1 <= r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros r1 r2 r3 Hle Hlt.
  unfold Rle in Hle.
  destruct Hle as [Heq | Hlt1].
lra.
lra.
Qed.
Lemma eq_equiv_1: forall (a b: R), a = b <-> (forall (eps: R), eps > 0 -> Rabs (a - b) < eps).
Proof.
  intros.
  split.
  intros.
  rewrite H.
  rewrite Rminus_diag.
  trivial.
  rewrite Rabs_R0. 
  trivial.
  intros.
  apply eq_implies_not_neq.
  intros.
  apply not_eq_1 in H0.
  destruct H0 as [eps [H_eps H_abs]].
  specialize (H eps H_eps).
  rewrite H_abs in H.
  lra.
Qed.
(* Właściwy dowód *)
Theorem Unambiguous_limit:  forall (s: sequence) (g_1 g_2: R), (limit_g s g_1 /\ limit_g s g_2 -> g_1 = g_2). 
Proof.
  intros.
  destruct H.
  unfold limit_g in H.
  unfold limit_g in H0.
  apply eq_equiv_1.
  intros.
  assert (eps2_pos : eps / 2 > 0) by lra.
  destruct (H (eps / 2) eps2_pos) as [N1 HN1].
  destruct (H0 (eps / 2) eps2_pos) as [N2 HN2].
  set (N := max N1 N2).
  specialize (HN1 N (Nat.le_max_l N1 N2)).
  specialize (HN2 N (Nat.le_max_r N1 N2)).
  assert (Rabs (g_1 - s N) = Rabs (s N - g_1)) by apply Rabs_minus_sym.
  assert (g_1 - g_2 = (g_1 - s N) + (s N - g_2)) by ring.
  rewrite H3.

  assert (triangle_ineq : Rabs ((g_1 - s N) + (s N - g_2)) <= Rabs (g_1 - s N) + Rabs (s N - g_2)).
  {
    apply Rabs_triang.
  }
lra.
Qed.
(* Trzeci podpunkt - dowód zbieżności ciągu stałego do granicy oraz dowód zbieżności ciągu stałego*)

Definition seq_const_0 (n : nat) : R :=
  match n with
  | O => 0
  | S n' => 0
  end.

Theorem Seq_0_coverges_to_0 : limit_g seq_const_0 0%R.
Proof.
unfold limit_g.
assert (H1 : 0 - 0 = 0).
{
lra.
}
assert (H2 : Rabs 0 = 0).
{
unfold Rabs.
destruct Rcase_abs.
lra.
lra.
}
intros.
exists 0 % nat.
intros.

destruct n.
unfold seq_const_0.
rewrite H1 in *.

rewrite H2.
lra.
unfold seq_const_0.
assert (0-0=0) by lra.
rewrite H1.
rewrite H2.
lra.
Qed.
(* Dowód, że ciąg stały jest zbieżny*)
Theorem Seq_0_coverges : limit seq_const_0.
Proof.
unfold limit.
exists 0.
apply Seq_0_coverges_to_0.
Qed.

(*Dziękujemy za uwagę, mamy nadzieję, że się podobało*)

