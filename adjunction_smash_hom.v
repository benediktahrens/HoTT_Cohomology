Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
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

Variable g : A .-> (pt_map_pt B C).

Definition out_of_smash_carrier : smash AB -> C.
apply (smash_elim_simp 
        (f:=fun (a : A) (b : B) => (pr1 (g a) b)) 
        (Ya := pr1 (g (point A)) (point B))
        (Yb := pr1 (g (point A)) (point B))).
intro a.
pathvia (point C).
  apply (pr2 (g a)).
  apply (!pr2 (g (point A))).

intro b.
pathvia (point C).

(*  change (point C) with  ((fun _ : B => point C) b). *)
  apply (happly (base_path (pr2 g))).

  apply (!happly (base_path (pr2 g)) _ ).
Defined.

Definition smash_uncurry : smash AB .-> C.
exists out_of_smash_carrier.
simpl.
unfold out_of_smash_carrier.
pathvia (pr1 (g (point A)) (point B)).
apply smash_elim_simp_pair.
apply (pr2 (g (point A))).
Defined.

End out_of_smash_from_into_hom.

Section into_hom_from_out_of_smash.

Variable f : smash AB .-> C.

Definition curry_carrier (a : A) : B .-> C.
 exists (fun b => f (smash_pair _ a b)).
 pathvia (f (smash_pair _ (point A)(point B))).
 - apply (map f (edge_connected_1 _ _ )).
 - apply (pr2 f).
Defined.

Lemma smash_curry_pr1 : 
  pr1 (curry_carrier (point A)) = pr1 (pt_map_null B C).
simpl.
  apply (strong_to_naive_funext strong_funext _ _ _ ).
  intro x.
   pathvia (f (smash_pair _ (point A)(point B))).
   apply (map f (edge_connected_2 _ _ )).
   apply (pr2 f).
Defined.

Definition smash_curry : A .-> (pt_map_pt B  C).
exists curry_carrier. simpl.
apply (total_path (p:=smash_curry_pr1)).
(*Check pr2 (curry_carrier (point A)).
rewrite transport_happly. *)
pathvia (! happly smash_curry_pr1 (point B) @ 
            pr2 (curry_carrier (point A))).
+ apply transport_happly.

+ unfold smash_curry_pr1. 
(* rewrite strong_funext_compute.
*)
  pathvia (opposite (map f (edge_connected_2 AB (point B)) @ pr2 f) @
     pr2 (curry_carrier (point A))).
  - apply whisker_right.
  apply map.
  apply (strong_funext_compute strong_funext B C
            (fun b : B => f (smash_pair _ (point A) b ))
           (fun _ : B => point C)).
  - simpl.
    pathvia (! (pr2 f) @ map f (edge_connected_1 AB (point A)) @ pr2 f).
    * apply whisker_right.
      apply map.
      change (pr2 f) with (idpath @ pr2 f) at 2.
      apply whisker_right.
      simpl.
      change (idpath _ ) with
          (map f (idpath (smash_pair AB (point A)(point B)) )).
      apply map. apply edge_connected_2_refl.
    * pathvia (! (pr2 f) @ pr2 f).
      { apply whisker_left.
        change (pr2 f) with (map f (idpath _) @ pr2 f) at 2.
        apply whisker_right.
        apply map. apply edge_connected_1_refl.
      }  apply opposite_left_inverse.
Defined. 

End into_hom_from_out_of_smash.

Section uncurry_after_curry.

Variable f : smash AB .-> C.

Lemma uncurry_after_curry_pair :
     forall a b,
     pr1 (smash_uncurry (smash_curry f)) (smash_pair AB a b) = 
             pr1 f (smash_pair AB a b).
Proof.
  intros a b.
  apply smash_elim_simp_pair.
Defined.

Lemma uncurry_after_curry_base_1:
     pr1 (smash_uncurry (smash_curry f)) (base_1 AB) = 
             pr1 f (base_1 AB).
Proof.
  unfold smash_uncurry.
  simpl.
  unfold out_of_smash_carrier.
  pathvia (point C).
  + apply smash_elim_simp_base_1.
  + pathvia (pr1 f (smash_pair AB (point A)(point B))).
    - apply (!pr2 f).
    - apply map.
      apply contract_1.
Defined. 

Lemma uncurry_after_curry_base_2:
     pr1 (smash_uncurry (smash_curry f)) (base_2 AB) = 
             pr1 f (base_2 AB).
Proof.
  unfold smash_uncurry.
  simpl.
  unfold out_of_smash_carrier.
  pathvia (point C).
  + apply smash_elim_simp_base_2.
  + pathvia (pr1 f (smash_pair AB (point A)(point B))).
    - apply (!pr2 f).
    - apply map.
      apply contract_2.
Defined. 

Lemma uncurry_after_curry :
     pr1 (smash_uncurry (smash_curry f)) = pr1 f.
Proof.
  simpl.
  apply (strong_to_naive_funext strong_funext _ _ _ ).
  simpl.
Check smash_elim.
  intro x.
(*  destruct f as [ f' p].*)
  simpl.
  apply (@smash_elim A B AB (fun x =>  
             out_of_smash_carrier (smash_curry f) x = pr1 f x)
        uncurry_after_curry_pair
        uncurry_after_curry_base_1
        uncurry_after_curry_base_2). 
  intro a.
  unfold uncurry_after_curry_base_1. 
  unfold uncurry_after_curry_pair.
  simpl. 
  rewrite constmap_map.
  rewrite <- compose_map.
  rewrite idpath_map.
  rewrite <- opposite_map.
  rewrite <- concat_map.
  rewrite <- smash_comp_contract_1.
  rewrite contract_1_refl.
  destruct f as [f'  p]. simpl.
    
  

  unfold smash_elim_simp_pair.
  destruct f as [f' p].
  simpl in *.
  elim p.
  simpl.
  
  rewrite transport_happly.
  rewrite smash_comp_base_1.
  
  simpl.
  
  apply 


Lemma uncurry_after_curry : forall f : smash AB .-> C,
     smash_uncurry (smash_curry f) = f.
Proof.
 intro f.
  

Lemma curry_after_uncurry_pr1 :
  forall f : A .-> pt_map_pt B C,
  forall a : A,
paths (pr1 (curry_carrier (smash_uncurry f) a)) (pr1 (pr1 f a)).
Proof.
 intro f.
 intro a.
apply (strong_to_naive_funext strong_funext _ _ _ ).
intro b.
simpl.
unfold out_of_smash_carrier.
apply smash_elim_simp_pair.
Defined.

Lemma curry_after_uncurry : forall f : A .-> pt_map_pt B C,
  pr1 (smash_curry (smash_uncurry f)) = pr1 f.
Proof.
intro f.
simpl.
apply (strong_to_naive_funext strong_funext _ _ _ ).
intro a.
assert (H: pr1 (curry_carrier (smash_uncurry f) a) =
           pr1 (pr1 f a)).
apply (strong_to_naive_funext strong_funext _ _ _ ).
intro b.
simpl.
unfold out_of_smash_carrier.
apply smash_elim_simp_pair.
apply (total_path (p:=curry_after_uncurry_pr1 f a)).
(* rewrite transport_happly. *)
pathvia (! (happly (curry_after_uncurry_pr1 f a) (point B)) @
   pr2 (curry_carrier (smash_uncurry f) a)).
apply transport_happly.
unfold curry_after_uncurry_pr1.
rewrite strong_funext_compute.
simpl.
unfold smash_elim_simp_pair.
Check (smash_elim_simp_pair).
rewrite 
pathvia (! (happly H (point B)) @ 
      pr2 (curry_carrier (smash_uncurry f) a)).
apply transport_happly.
unfold H.
simpl.
  Check (pr2 (pr1 f a)).
  unfold smash_elim_simp_pair.
  simpl.
  simpl.
  rewrite 
rewrite transport_happly.
unfold curry_carrier.
assert (H: (fun b : B => (smash_uncurry f) (smash_pair AB a b))
            = pr1 (pr1 f a)).
apply (strong_to_naive_funext strong_funext _ _ _ ).
intro b.
simpl.
unfold out_of_smash_carrier.
apply smash_elim_simp_pair.
  Check (pr1 f a).

assert (H' : pr1 (fun b : B => (smash_uncurry f) (smash_pair AB a b);
  map (smash_uncurry f) (edge_connected_1 AB a) @ pr2 (smash_uncurry f))
      = pr1 (pr1 f a)).
apply (total_path (p:= H)).

simpl.
  
rewrite smash_elim_sipm
simpl.

Lemma curry_after_uncurry : forall f : A .-> pt_map_pt B C,
  smash_curry (smash_uncurry f) = f.
Proof.
intro f.



End maps_in_each_direction.














