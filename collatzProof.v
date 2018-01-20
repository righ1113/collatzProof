
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





