From mathcomp
     Require Import ssreflect.

Section Magma.
  Record magma : Type :=
    Magma {
        carrier : Type;
        operator : carrier -> carrier ->  carrier
      }.

  Definition prop_and_magma := Magma Prop and.

  Definition nat_plus_magma := Magma nat plus.

  Lemma PropMagmaFalse2 (x y : Prop) :
    operator prop_and_magma x False -> y.

End Magma.
