Set Implicit Arguments.
Unset Strict Implicit.

Require Import HoTT.Homotopy.
Require Import ExtensionalityAxiom.
Require Import pointed_spaces.
Require Import smash_product.

Import pt_map_notation.
Import smash_notation.

Section maps_in_each_direction.

Variables A B C : pt_type.
Variable AB : smash_data A B.

Section out_of_smash_from_into_hom.

Variable f : pt_map A (pt_map_pt B C).

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

Section into_hom_from_out_of_smash.

Variable f : smash AB .-> C.

Definition curry_carrier (a : A) : B .-> C.
 exists (fun b => f (smash_pair _ a b)).
 transitivity (f (smash_pair _ (point A)(point B))).
 - apply (map f (edge_connected_1 _ _ )).
 - rewrite <- (pr2 f).
   reflexivity.
Defined.

Lemma smash_curry_pr1 : 
  pr1 (curry_carrier (point A)) = pr1 (pt_map_null B C).
simpl.
  apply (strong_to_naive_funext strong_funext _ _ _ ).
  intro x.
  transitivity (f (smash_pair _ (point A)(point B))).
   apply (map f (edge_connected_2 _ _ )).
   rewrite <- (pr2 f).
   reflexivity.
Defined.

Definition smash_curry : A .-> (pt_map_pt B  C).
exists curry_carrier.
apply (total_path (p:=smash_curry_pr1)).
rewrite transport_happly.
unfold smash_curry_pr1.
rewrite strong_funext_compute. 
 simpl.


(* this fails; do i have correct paths above? *)
apply opposite_left_inverse.
  rewrite trans_trivial.
            (pr1 f) (pr1 pt_initial)).
apply funext.
unfold curry_carrier. simpl.

End carrier.



End into_hom_from_out_of_smash.

End maps_in_each_direction.














