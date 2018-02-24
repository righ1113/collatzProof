
Axiom DNE1: forall(P: Prop), ~~P->P.
Axiom DNE2: forall(P: Prop), P->~~P.
Axiom smaller: nat -> Prop.
Axiom lemma1_3: forall(n:nat), ~smaller(S (S n)) -> ~smaller(S n).
Axiom lemma2: smaller 0.
Axiom lemma3: smaller 1.

Lemma contraposition:
  forall(A B:Prop), (~B->~A)->(A->B).
Proof.
  intros.
  assert (forall(A B:Prop), (~B->~A)->(~~A->~~B)).
    tauto.
  apply H1 in H.
  apply DNE1 in H.
  auto.
  apply DNE2 in H0.
  auto.
Qed.

Lemma lemma1_4:
  forall(n:nat), smaller(S n) -> smaller(S (S n)).
Proof.
  intro.
  apply contraposition.
  apply lemma1_3.
Qed.

Theorem proof:
  forall(n:nat), smaller n.
Proof.
  intro.
  induction n.
    apply lemma2.
    induction n.
      apply lemma3.
      assert (forall(n:nat), smaller(S n) -> smaller(S (S n))).
        apply lemma1_4.
      apply H in IHn.
      auto.
Qed.

(* ---------------------------- *)
Axiom infinity: Prop.
Axiom smaller2: nat -> nat -> Prop.
Axiom lemma4: forall(k y:nat), ~smaller2 (S (S k)) y -> ~smaller2 (S k) y.
Axiom lemma5: forall(k y:nat), smaller2 (S k) y -> smaller2 (S k) (S y).
Axiom lemma6: forall(k y:nat), infinity -> ~smaller2 (S (S k)) (S y).
Axiom lemma7: forall(k y:nat), smaller2 (S k) y.

Lemma lemma8:
  forall(k y:nat), smaller2 (S k) y -> smaller2 (S (S k)) y.
Proof.
  intro.
  intro.
  apply contraposition.
  apply lemma4.
Qed.

Theorem proof2: forall(k y:nat), infinity -> False.
Proof.
  intros.
  assert(infinity -> ~smaller2 (S (S k)) (S y)).
    apply lemma6.
  apply H0 in H.
  lazy in H.
  assert(smaller2 (S k) y).
    apply lemma7.
  apply lemma8 in H1.
  apply lemma5 in H1.
  apply H in H1.
  auto.
Qed.







