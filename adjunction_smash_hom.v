Set Implicit Arguments.
Unset Strict Implicit.

Require Import HoTT.Homotopy.
Require Import ExtensionalityAxiom.
Require Import pointed_spaces.
Require Import smash_product.
Require Import tactics.

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
apply (happly (base_path (pr2 f))).
Defined.

Definition smash_uncurry : smash AB .-> C.
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
 apply (concat (y:=f (smash_pair _ (point A)(point B)))).
 - apply (map f (edge_connected_1 _ _ )).
 - apply (pr2 f).
Defined.

Lemma smash_curry_pr1 : 
  pr1 (curry_carrier (point A)) = pr1 (pt_map_null B C).
simpl.
  apply (strong_to_naive_funext strong_funext _ _ _ ).
  intro x.
   apply (concat (y:=f (smash_pair _ (point A)(point B)))).
   apply (map f (edge_connected_2 _ _ )).
   apply (pr2 f).
Defined.

Definition smash_curry : A .-> (pt_map_pt B  C).
exists curry_carrier.
apply (total_path (p:=smash_curry_pr1)).
rewrite transport_happly.
unfold smash_curry_pr1.
rewrite strong_funext_compute.
rewrite edge_connected_2_refl.
simpl.
rewrite edge_connected_1_refl.
rewrite idpath_map.
rewrite idpath_left_unit.
apply opposite_left_inverse.
Defined. 

End into_hom_from_out_of_smash.

Lemma curry_after_uncurry : forall f : A .-> pt_map_pt B C,
  pr1 (smash_curry (smash_uncurry f)) = pr1 f.
Proof.
intro f.
simpl.
apply (strong_to_naive_funext strong_funext _ _ _ ).
intro a.
unfold curry_carrier.
  simpl.
rewrite smash_elim_sipm
simpl.

Lemma curry_after_uncurry : forall f : A .-> pt_map_pt B C,
  smash_curry (smash_uncurry f) = f.
Proof.
intro f.



End maps_in_each_direction.













