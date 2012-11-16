Set Implicit Arguments.
Unset Strict Implicit.

Require Import HoTT.Homotopy.
Require Import pointed_spaces.
Require Import smash_product.

Import pt_map_notation.

Section out_of_smash_from_into_hom.

Variables A B C : pt_type.
Variable f : pt_map A (pt_map_pt B C).

Variable AB : smash_data A B.

Definition ca : A -> B -> C.
intros a b.
  apply (pr1 (f a)).
  exact b.
Defined.
Print ca.
  

Definition out_of_smash_carrier : smash AB -> C.
apply (smash_elim_simp 
        (f:=fun (a : A) (b : B) => (pr1 (f a) b)) 
        (Ya := point C)
        (Yb := point C)).
intro a.
apply (pr2 (f a)).
intro b.
set (H:=pr2 f).
simpl in H.
unfold pt_map_null in H.
set (H':= base_path H).
simpl in H'.
set (H2 := happly H').
simpl in H2.
apply H2.
Defined.

Definition hom_to_smash_adj : smash AB .-> C.
exists out_of_smash_carrier.
simpl.
unfold out_of_smash_carrier.
  rewrite smash_elim_simp_pair.
  apply (pr2 (f (point A))).
Defined.

End out_of_smash_from_into_hom.














