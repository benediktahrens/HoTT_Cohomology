

Require Import HoTT.Homotopy.
Require Import ExtensionalityAxiom.

Set Implicit Arguments.
Unset Strict Implicit.


Record pt_type := {
 carrier :> Type ;
 point : carrier
}.

Record pt_map_record (A B : pt_type) := {
  carrier_map_record :> A -> B ;
  pt_path_record : carrier_map_record (point A) = point B
}.

Definition pt_map (A B : pt_type) := 
   {f : A -> B & f (point A) = point B}.

Definition pt_map_carrier (A B : pt_type) (f : pt_map A B) : A -> B :=
   projT1 f.

Coercion pt_map_carrier : pt_map >-> Funclass.

Definition pt_map_point (A B : pt_type) (f : pt_map A B) : 
    f (point A) = point B := projT2 f.


Definition pt_unit :=
 {| carrier := unit ; point := tt |}.

Canonical Structure pt_unit.


Section transport_shit.

Variables A B : pt_type.
Variables f g : pt_map A B.
(*
Variable H : pr1 f = pr1 g.
Variable p : f (point A) = point B.


Check (!(happly H (point A)) @ p).
Check transport (P := fun f : A -> B => f (point A) = point B) H p.
*)
Lemma transport_happly : forall (H : pr1 f = pr1 g),
   forall (p : f (point A) = point B),
  transport (P:= fun f : A -> B => f(point A) = point B) H p
    = !(happly H (point A)) @ p.
Proof.
  intros H.
  induction H.
  simpl.
  reflexivity.
Defined.

Lemma transport_happly_dep : forall (H : pr1 f = pr1 g),
   forall (p : f (point A) = point B),
  transport (P:= fun f : A -> B => f(point A) = point B) H p
    = !(happly_dep H (point A)) @ p.
Proof.
  intros H.
  induction H.
  simpl.
  reflexivity.
Defined.


End transport_shit.



Section pt_unit_initial_terminal.

Variable A : pt_type.

Definition pt_initial : pt_map pt_unit A := 
   (fun _ => point A ; identity_refl).

Definition pt_terminal : pt_map A pt_unit := 
  (fun (a : A) => tt (*point pt_unit*) ; identity_refl).

Section initial_terminal.
(*
Variable mfunext : forall (X Y : Type) (f g : X -> Y),
      (forall x, f x = g x) -> f = g.
*)

Lemma pt_initiality_pr1 : 
     forall f : pt_map pt_unit A, pr1 f = pr1 pt_initial.
Proof.
  intro f.
  
  set (H := strong_to_naive_funext strong_funext _ _ 
            (pr1 f) (pr1 pt_initial)).
  apply H.
(*  apply (strong_to_naive_funext_dep  strong_funext_dep ). *)
  intro x.
  induction x. 
  apply (pt_map_point f).
Defined.


Lemma pt_intiality : is_contr (pt_map pt_unit A).
Proof.
  exists pt_initial.
  intro f.
(*
  assert (H : pr1 f = pr1 pt_initial).
    simpl.
    apply strong_funext. 
    intro x.
    induction x. 
    apply (pt_map_point f).
*)
  apply (@total_path _ _ _ _ (pt_initiality_pr1 f)).
  rewrite transport_happly.
  unfold pt_initiality_pr1.
  rewrite strong_funext_compute.
  simpl.
  unfold pt_map_point.
  apply opposite_left_inverse.
Defined.
  transitivity (
     ! (happly_dep (
  unfold pt_dumb.
  simpl.
  rewrite strong_funext_dep_compute.
  
  apply opposite_left_inverse.
  Check (pr2 pt_initial).
  simpl.
  Check H.
  Check (pr2 f). 
  Check 
  Print happly.
  set (H' := happly H tt).
  simpl in H'.
  transitivity (
  rewrite trans_trivial.
  induction H.
  


Variable f : pt_map pt_unit A.






