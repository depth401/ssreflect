From mathcomp
     Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition mySet (M : Type) := M -> Prop.

Definition belong {M : Type} (A : mySet M) (x : M) :
  Prop := A x.
Notation "x ∈ A" := (belong A x) (at level 11).

Axiom axiom_mySet : forall (M : Type) (A : mySet M),
    forall (x : M), (x ∈ A) \/ ~(x ∈ A).

Definition myEmptySet { M : Type} : mySet M := fun _ => False.
Definition myMotherSet { M : Type} : mySet M := fun _ => True.

Definition mySub {M} := fun (A B : mySet M) =>
                          (forall (x : M), (x ∈ A) -> (x ∈ B)).
Notation "A ⊂ B" := (mySub A B) (at level 11).

Section 包含関係.
  Variable M : Type.

  Lemma Sub_Mother (A : mySet M) : A ⊂ myMotherSet.
  Proof.
      by [].
  Qed.

  Lemma Sub_Empty (A : mySet M) : myEmptySet ⊂ A.
  Proof.
      by [].
  Qed.

  Lemma rfl_Sub (A : mySet M) : (A ⊂ A).
  Proof.
      by[].
  Qed.

  Lemma transitive_Sub (A B C : mySet M) :
    (A ⊂ B) -> (B ⊂ C) -> (A ⊂ C).
  Proof.
    move=> H1 H2 t H3.
    apply: H2.
    by apply: H1.
  Qed.

End 包含関係.

Definition eqmySet {M : Type} :=
  fun (A B : mySet M) => (A ⊂ B /\ B ⊂ A).
Axiom axiom_ExteqmySet : forall {M : Type} (A B :mySet M),
    eqmySet A B -> A = B.

Section 等号.
  Variable Mother : Type.

  Lemma rfl_eqS (A : mySet Mother) : A = A.
  Proof.
      by [].
  Qed.

  Lemma sym_eqS (A B : mySet Mother) : A = B -> B = A.
  Proof.
      by [].
  Qed.
End 等号.

Definition myComplement {M : Type} (A : mySet M) : mySet M :=
  fun (x : M) => ~(A x).
Notation "A ^c" := (myComplement A) (at level 11).

Definition myCup {M : Type} (A B : mySet M) : mySet M :=
  fun (x : M) => (x ∈ A) \/ (x ∈ B).
Notation "A ∪ B" := (myCup A B) (at level 11).

Section 演算.
  Variable M : Type.

  Lemma cEmpty_Mother : (@myEmptySet M)^c = myMotherSet.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    apply: conj.
    rewrite /mySub.
    rewrite /myComplement.
    rewrite //.
    rewrite /mySub.
    move=> H1 H2.
    rewrite /myComplement.
    rewrite //.
  Qed.

  Lemma cc_cancel (A : mySet M) : (A^c)^c = A.
  Proof.
    apply axiom_ExteqmySet.
    rewrite /eqmySet.
    apply conj.
    rewrite /mySub.
    rewrite /myComplement.
    move=> x H.
    by case: (axiom_mySet A x).
    rewrite /mySub.
    rewrite /myComplement.
    move=> x H.
    rewrite //.
  Qed.

  Lemma cMother_Empty : (@myMotherSet M)^c = myEmptySet.
  Proof.
    rewrite -cEmpty_Mother.
    by rewrite cc_cancel.
  Qed.

  Lemma myCupA (A B C : mySet M) : (A ∪ B) ∪ C = A ∪ (B ∪ C).
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    rewrite /mySub.
    apply: conj.
    move=> x [H1 | H2].
    - case: H1 => t.
      + by apply: or_introl.
      + apply: or_intror.
        by apply: or_introl.
    - apply: or_intror.
      by apply: or_intror.
    move=> x [H1 | H2].
    apply: or_introl.
    by apply: or_introl.
    - case: H2 => t.
      + apply: or_introl.
        by apply: or_intror .
      + by apply: or_intror.
  Qed.

  Lemma myUnionCompMother (A : mySet M) : A ∪ (A^c) = myMotherSet.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    apply: conj.
    - by apply: Sub_Mother.
    - rewrite /mySub.
      move=> x H.
      by apply: axiom_mySet.
  Qed.
End 演算.


Definition myMap {M1 M2 : Type} (A : mySet M1) (B : mySet M2) (f : M1 -> M2) :=
  (forall (x : M1), (x ∈ A) -> ((f x) ∈ B)).
Notation "f ∈Map A \to B" := (myMap A B f) (at level 11).

Definition MapCompo {M1 M2 M3 : Type} (f : M2 -> M3) (g : M1 -> M2) : M1 -> M3 :=
  fun (x : M1) => f (g x).
Notation "f ・ g" := (MapCompo f g) (at level 11).

Definition ImgOf {M1 M2 : Type} (f : M1 -> M2) {A : mySet M1} {B : mySet M2} (_ : f ∈Map A \to B) : mySet M2
  := fun (y : M2) => (exists (x : M1), y = f x /\ x ∈ A).

Definition mySetInj {M1 M2 : Type} (f : M1 -> M2) (A : mySet M1) (B : mySet M2) (_ : f ∈Map A \to B) :=
  forall (x y : M1), (x ∈ A) -> (y ∈ A) -> (f x = f y) -> (x = y).

Definition mySetSur {M1 M2 : Type} (f : M1 -> M2) (A : mySet M1) (B : mySet M2) (_ : f ∈Map A \to B) :=
  forall (y : M2), (y ∈ B) -> (exists (x : M1), (x ∈ A) -> (f x = y)).

Definition mySetBi {M1 M2 : Type} (f : M1 -> M2) (A : mySet M1) (B : mySet M2) (fAB : f ∈Map A \to B) :=
  (mySetInj fAB) /\ (mySetSur fAB).

Section 写像.
  Variables M1 M2 M3 : Type.
  Variable f : M2 -> M3.
  Variable g : M1 -> M2.
  Variable A : mySet M1.
  Variable B : mySet M2.
  Variable C : mySet M3.
  Hypothesis gAB : g ∈Map A \to B.
  Hypothesis fBC : f ∈Map B \to C.

  Lemma transitive_Inj (fgAC : (f ・ g) ∈Map A \to C) :
    mySetInj fBC -> mySetInj gAB -> mySetInj fgAC.
  Proof.
    rewrite /mySetInj.
    move=> Hinjf Hinjg x y HxA HyA H.
    apply: (Hinjg x y HxA HyA).
    apply: (Hinjf (g x) (g y)).
    + by apply: gAB.
    + by apply: gAB.
    + by rewrite //.
  Qed.

  Lemma CompoTrns : (f ・ g) ∈Map A \to C.
  Proof.
    move: gAB fBC.
    rewrite /MapCompo /myMap.
    move=> Hab Hbc t Ha.
    by move: (Hbc (g t) (Hab t Ha)).
  Qed.

  Lemma ImSub : (ImgOf gAB) ⊂ B.
  Proof.
    rewrite /mySub.
    move=> x.
    case => x0.
    case => H1 H2.
    rewrite H1.
    by apply: gAB.
  Qed.

End 写像.

Variable M : finType.

Definition p2S (pA : pred M) : mySet M :=
  fun (x : M) =>
    if (x \in pA) then True else False.
Notation "\{  x 'in' pA \}" := (p2S pA).

Section fintypeを用いた有限集合.
  Lemma Mother_predT : myMotherSet = \{ x in M \}.
  Proof.
      by [].
  Qed.

  Lemma myFinBelongP (x : M) (pA : pred M) : reflect (x ∈ \{ x in pA \}) (x \in pA).
  Proof.
    rewrite /belong.
    rewrite /p2S.
    apply/ (iffP idP) => H1.
    - by rewrite (_ : (x \in pA) = true).
    -
      + have testH : (x \in pA) || ~~(x \in pA).
        set t := x \in pA.
        by case: t.
      + move: testH.
        case/ orP => [ | Harg].
        by [].
        rewrite (_ : (x \in pA) = false) in H1.
        by [].
        by apply: negbTE.
  Qed.

  Lemma myFinSubsetP (pA pB : pred M) : reflect (\{ x in pA \} ⊂ \{ x in pB \}) (pA \subset pB).
  Proof.
    rewrite /mySub; apply/ (iffP idP) => H.
    - move=> x /myFinBelongP => H2.
      apply/ myFinBelongP.
      move: H => /subsetP.
      by rewrite /sub_mem; apply.
    - apply/ subsetP.
      rewrite /sub_mem => x /myFinBelongP => HpA.
      by apply/ myFinBelongP; apply H.
  Qed.

  Lemma Mother_Sub (pA : pred M) :
    myMotherSet ⊂ \{ x in pA \} -> forall x, x ∈ \{ x in pA \}.
  Proof.
    rewrite Mother_predT => /myFinSubsetP => H x; apply /myFinBelongP.
    by apply: predT_subset.
  Qed.

  Lemma transitive_Sub' (pA pB pC : pred M) :
    \{ x in pA \} ⊂ \{ x in pB \} -> \{ x in pB \} ⊂ \{ x in pC \} -> \{ x in pA \} ⊂ \{ x in pC \}.
  Proof.
    move /myFinSubsetP => HAB /myFinSubsetP => HBC.
    by apply /myFinSubsetP /(subset_trans HAB HBC).
  Qed.

  Lemma transitive_Sub'' (pA pB pC : pred M) :
    \{ x in pA \} ⊂ \{ x in pB \} -> \{ x in pB \} ⊂ \{ x in pC \} -> \{ x in pA \} ⊂ \{ x in pC \}.
  Proof.
    by apply: transitive_Sub.
  Qed.
End fintypeを用いた有限集合.
