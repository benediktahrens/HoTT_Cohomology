

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



Module Import pt_map_notation.

Notation "A .-> B" := (pt_map A B) (at level 55).
(*Notation "A '_o'" := (point A) (at level 4).*)

End pt_map_notation.

Definition pt_map_null (A B : pt_type) : A .-> B := 
  existT _ (fun _ : A => point B) idpath .

Definition pt_map_pt (A B : pt_type) : pt_type := {|
   carrier := A .-> B ;
   point := pt_map_null A B |}.


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
Variables f g : A .-> B.

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

Definition pt_initial : pt_unit .-> A := 
   (fun _ => point A ; identity_refl).

Definition pt_terminal : A .-> pt_unit := 
  (fun (a : A) => tt (*point pt_unit*) ; identity_refl).

Section initial_terminal.
(*
Variable mfunext : forall (X Y : Type) (f g : X -> Y),
      (forall x, f x = g x) -> f = g.
*)

Lemma pt_initiality_pr1 : 
     forall f : pt_unit .-> A, pr1 f = pr1 pt_initial.
Proof.
  intro f.
  apply (strong_to_naive_funext strong_funext _ _ 
            (pr1 f) (pr1 pt_initial)).
  intro x;
  induction x. 
  apply (pt_map_point f).
Defined.


Lemma pt_intiality : is_contr (pt_unit .-> A).
Proof.
  exists pt_initial.
  intro f.
  apply (@total_path _ _ _ _ (pt_initiality_pr1 f)).
  rewrite transport_happly.
  unfold pt_initiality_pr1.
  rewrite strong_funext_compute.
  simpl.
  unfold pt_map_point.
  apply opposite_left_inverse.
Defined.


Lemma pt_terminality_pr1 : 
     forall f : A .-> pt_unit, pr1 f = pr1 pt_terminal.
Proof.
  intro f.
  apply (strong_to_naive_funext strong_funext _ _ _ _ ).
(*            (pr1 f) (pr1 pt_terminal)). *)
  intro x. 
  apply (pr2 unit_contr).
Defined.

Lemma pt_terminality : is_contr (A .-> pt_unit).
Proof.
  exists pt_terminal.
  intro f.
  apply (@total_path _ _ _ _ (pt_terminality_pr1 _ )).
  rewrite transport_happly.
  unfold pt_terminality_pr1.
  rewrite strong_funext_compute.
  apply (contr_path2).  
  exact unit_contr.
Defined.

End initial_terminal.

End pt_unit_initial_terminal.


Section pt_map_composition.

Variables A B C : pt_type.
Variable f : A .-> B.
Variable g : B .-> C.

Definition pt_map_compose : A .-> C.
exists (fun x => g (f x)).
transitivity (g (point B)).
exact (map g (pr2 f)). 
exact (pr2 g).
Defined.

End pt_map_composition.




