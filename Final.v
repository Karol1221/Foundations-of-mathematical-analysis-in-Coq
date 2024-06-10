Require Import Reals.
Open Scope R_scope.
Require Import Lra. (* Linear Reals Arith *)
Require Import Classical.
Require Import ZArith.

(* pierwszy podpunkt - definicja ciągu, zbieżności do granicy i zbieżności *)

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
  (* a <> b -> istnieje eps > 0, że Rabs (a - b) = eps *)
  intros H.
  exists (Rabs (a - b)).
  split.
  (* Pokażemy, że Rabs (a - b) > 0, co implikuje, że a nie jest równe b *)
  apply Rabs_pos_lt.
  unfold not.
  intros.
  apply H.
  apply Rminus_diag_uniq.
  exact H0.
  reflexivity.
  (* (istnieje eps > 0, że Rabs (a - b) = eps) -> a <> b *)
  intros [eps [H_eps H_eq]].
  unfold not.
  intros H_eq_ab.
  (* Zakładając, że a = b, prowadzi to do sprzeczności z faktem, że Rabs (a - b) = eps > 0 *)
  rewrite H_eq_ab in H_eq.
  rewrite Rminus_eq_0 in H_eq.
  rewrite Rabs_R0 in H_eq.
  lra.
Qed.

Lemma eq_implies_not_neq : forall (a b : R), a = b <-> (a <> b -> False).
Proof.
  intros.
  split.
  (* Jeśli a = b, to a <> b jest fałszem *)
  intros.
  unfold not in H0.
  rewrite H in H0.
  apply H0.
  reflexivity.
  (* Jeśli a <> b implikuje fałsz, to a = b *)
  intros.
  unfold not in H.
  apply NNPP in H.
  rewrite H.
  trivial.
Qed.

Lemma Rle_trans_lt : forall r1 r2 r3 : R, r1 <= r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros r1 r2 r3 Hle Hlt.
  (* Przechodniość nierówności: jeśli r1 <= r2 i r2 < r3, to r1 < r3 *)
  unfold Rle in Hle.
  destruct Hle as [Heq | Hlt1].
  (* Przypadek, gdy r1 = r2 *)
  lra.
  (* Przypadek, gdy r1 < r2 *)
  lra.
Qed.

Lemma eq_equiv_1: forall (a b: R), a = b <-> (forall (eps: R), eps > 0 -> Rabs (a - b) < eps).
Proof.
  intros.
  split.
  (* Jeśli a = b, to różnica między nimi jest mniejsza od dowolnego eps *)
  intros.
  rewrite H.
  rewrite Rminus_diag.
  trivial.
  rewrite Rabs_R0. 
  trivial.
  (* Jeśli różnica między a i b jest mniejsza od dowolnego eps, to a = b *)
  intros.
  apply eq_implies_not_neq.
  intros.
  apply not_eq_1 in H0.
  destruct H0 as [eps [H_eps H_abs]].
  (* Używając hipotezy, że różnica jest mniejsza od eps, dochodzimy do sprzeczności *)
  specialize (H eps H_eps).
  rewrite H_abs in H.
  lra.
Qed.

(* Właściwy dowód jednoznaczności wyznaczenia granicy *)
Theorem Unambiguous_limit:  forall (s: sequence) (g_1 g_2: R), (limit_g s g_1 /\ limit_g s g_2 -> g_1 = g_2). 
Proof.
  intros.
  destruct H. (* Rozbijamy hipotezę na dwie części *)
  unfold limit_g in H. (* Rozwijamy definicję zbieżności do granicy g_1 *)
  unfold limit_g in H0. (* Rozwijamy definicję zbieżności do granicy g_2 *)
  apply eq_equiv_1. (* Zastosowanie równoważności z lematem eq_equiv_1 *)
  intros.
  (* Podzielmy eps na pół, aby wykorzystać własność trójkąta *)
  assert (eps2_pos : eps / 2 > 0) by lra.
  (* Znajdź odpowiednie N1 dla g_1 *)
  destruct (H (eps / 2) eps2_pos) as [N1 HN1].
  (* Znajdź odpowiednie N2 dla g_2 *)
  destruct (H0 (eps / 2) eps2_pos) as [N2 HN2].
  (* Wybierzmy N jako maksymalne z N1 i N2 *)
  set (N := max N1 N2).
  (* Użyjmy odpowiednich właściwości dla N *)
  specialize (HN1 N (Nat.le_max_l N1 N2)).
  specialize (HN2 N (Nat.le_max_r N1 N2)).
  (* Pokażmy, że różnica jest mniejsza od eps *)
  assert (Rabs (g_1 - s N) = Rabs (s N - g_1)) by apply Rabs_minus_sym.
  assert (g_1 - g_2 = (g_1 - s N) + (s N - g_2)) by ring.
  rewrite H3.

  (* Zastosuj nierówność trójkąta *)
  assert (triangle_ineq : Rabs ((g_1 - s N) + (s N - g_2)) <= Rabs (g_1 - s N) + Rabs (s N - g_2)).
  {
    apply Rabs_triang.
  }
  (* Finalne zakończenie dowodu, wykorzystując fakt, że obie wartości są mniejsze od eps/2 *)
  lra.
Qed.

(* Trzeci podpunkt - dowód zbieżności ciągu stałego do granicy oraz dowód zbieżności ciągu stałego *)

(* Definicja ciągu stałego przyjmującego wartość 0 *)
Definition seq_const_0 (n : nat) : R :=
  match n with
  | O => 0
  | S n' => 0
  end.

(* Dowód, że ciąg stały seq_const_0 jest zbieżny do 0 *)
Theorem Seq_0_coverges_to_0 : limit_g seq_const_0 0%R.
Proof.
  unfold limit_g. (* Rozwijamy definicję zbieżności do granicy 0 *)
  assert (H1 : 0 - 0 = 0). (* Pokażemy, że różnica 0 - 0 wynosi 0 *)
  {
    lra.
  }
  assert (H2 : Rabs 0 = 0). (* Pokażemy, że wartość bezwzględna z 0 to 0 *)
  {
    unfold Rabs.
    destruct Rcase_abs.
    lra.
    lra.
  }
  intros.
  (* Dowód, że dla dowolnego eps > 0 istnieje N = 0 spełniające warunki *)
  exists 0%nat.
  intros.
  destruct n.
  unfold seq_const_0.
  rewrite H1 in *.
  rewrite H2.
  lra.
  unfold seq_const_0.
  assert (0 - 0 = 0) by lra.
  rewrite H1.
  rewrite H2.
  lra.
Qed.

(* Dowód, że ciąg stały jest zbieżny *)
Theorem Seq_0_coverges : limit seq_const_0.
Proof.
  unfold limit. (* Rozwijamy definicję istnienia granicy *)
  exists 0. (* Wybieramy granicę jako 0 *)
  apply Seq_0_coverges_to_0. (* Zastosowanie poprzedniego dowodu *)
Qed.

(*Dziękujemy za uwagę, mamy nadzieję, że się podobało*)
