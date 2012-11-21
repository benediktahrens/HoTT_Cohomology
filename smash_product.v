
Set Implicit Arguments.
Unset Strict Implicit.

Require Import HoTT.Homotopy.
Require Import pointed_spaces.
Require Import tactics.

Import pt_map_notation.


Section smash_product.

Variables A B : pt_type.

Reserved Notation "< A , B >"
 (at level 40, B at next level, left associativity).

Record smash_data : Type := {
  smash_carrier :> Type ;
  smash_pair : forall (a : A) (b : B), smash_carrier 
    where "< a , b >" := (smash_pair a b)  
;
  base_1 : smash_carrier ;
  base_2 : smash_carrier ;
  contract_1 : forall (a : A), <a, point B> = base_1 ;
  contract_2 : forall (b : B), <point A, b> = base_2 ;
  
  smash_elim : forall (P : smash_carrier -> Type)
     (d_pair : forall a b, P (< a , b>) )
     (d_base_1 : P base_1)
     (d_base_2 : P base_2)
     (d_contract_1 : forall a : A,
        transport (contract_1 a) (d_pair a (point B)) = 
             d_base_1) 
     (d_contract_2 : forall b : B,
        transport (contract_2 b) (d_pair (point A) b) = 
             d_base_2) 
     
      , forall x : smash_carrier, P x
;
  smash_comp_pair : forall (P : smash_carrier -> Type)
     (d_pair : forall a b, P (< a , b>) )
     (d_base_1 : P base_1)
     (d_base_2 : P base_2)
     (d_contract_1 : forall a : A,
        transport (contract_1 a) (d_pair a (point B)) = 
             d_base_1) 
     (d_contract_2 : forall b : B,
        transport (contract_2 b) (d_pair (point A) b) = 
             d_base_2),
       forall a b,
       smash_elim  (*d_pair*) (*d_base_1*) (*d_base_2*) 
          d_contract_1 d_contract_2
            (<a, b>) = d_pair a b
;

  smash_comp_base_1 : forall (P : smash_carrier -> Type)
     (d_pair : forall a b, P (< a , b>) )
     (d_base_1 : P base_1)
     (d_base_2 : P base_2)
     (d_contract_1 : forall a : A,
        transport (contract_1 a) (d_pair a (point B)) = 
             d_base_1) 
     (d_contract_2 : forall b : B,
        transport (contract_2 b) (d_pair (point A) b) = 
             d_base_2),

       smash_elim  (*d_pair*) (*d_base_1*) (*d_base_2*) 
          d_contract_1 d_contract_2
            base_1 = d_base_1
;
 smash_comp_base_2 : forall (P : smash_carrier -> Type)
     (d_pair : forall a b, P (< a , b>) )
     (d_base_1 : P base_1)
     (d_base_2 : P base_2)
     (d_contract_1 : forall a : A,
        transport (contract_1 a) (d_pair a (point B)) = 
             d_base_1) 
     (d_contract_2 : forall b : B,
        transport (contract_2 b) (d_pair (point A) b) = 
             d_base_2),

       smash_elim  (*d_pair*) (*d_base_1*) (*d_base_2*) 
          d_contract_1 d_contract_2
            base_2 = d_base_2

;

  smash_comp_contract_1 : forall (P : smash_carrier -> Type)
     (d_pair : forall a b, P (< a , b>) )
     (d_base_1 : P base_1)
     (d_base_2 : P base_2)
     (d_contract_1 : forall a : A,
        transport (contract_1 a) (d_pair a (point B)) = 
             d_base_1) 
     (d_contract_2 : forall b : B,
        transport (contract_2 b) (d_pair (point A) b) = 
             d_base_2),
    forall a : A,
      map_dep (smash_elim d_contract_1 d_contract_2) (contract_1 a) =
          (map (transport (contract_1 a)) ((smash_comp_pair 
d_contract_1 d_contract_2) a (point B)))
              @ (d_contract_1 a) @
                ! (smash_comp_base_1 
d_contract_1 d_contract_2)

(* thanks PLL *)

}.


Definition smash_elim_simp (X : smash_data) 
      (Y : pt_type) 
     (f : forall (a : A) (b : B), Y) 
     (Ya Yb : Y)
     (Ha : forall a : A, f a (point B) = Ya)
     (Hb : forall b : B, f (point A) b = Yb) : X -> Y.
Proof.
  apply
   (smash_elim (P := (fun _ => Y))
                    (d_pair := f)
                    (d_base_1 := Ya) 
                    (d_base_2 := Yb)
                      ).
  intro a.
  pathvia (transport (P:=fun _ : X => Y)(contract_1 X a) Ya).
  apply (map _ (Ha a)).
  apply trans_trivial.
  intro b.
  pathvia (transport (P:=fun _ : X => Y)(contract_2 X b) Yb).
  apply (map _ (Hb b)).
  apply trans_trivial.
Defined.

Section smash_elim_simp_rules.

Variable X : smash_data.

Variables     (Y : pt_type) 
     (f : forall (a : A) (b : B), Y) 
     (Ya Yb : Y)
     (Ha : forall a : A, f a (point B) = Ya)
     (Hb : forall b : B, f (point A) b = Yb).

Lemma smash_elim_simp_pair : forall a b,
  @smash_elim_simp X _ f _ _ Ha Hb (smash_pair X a b) = f a b.
Proof.
  intros a b.
  apply  (@smash_comp_pair X (fun _ => Y) f Ya Yb).
Defined.

Lemma smash_elim_simp_base_1 : 
  @smash_elim_simp X _ f _ _ Ha Hb (base_1 X) = Ya.
Proof.
  apply (@smash_comp_base_1 X (fun _ => Y) f Ya Yb).
Defined.

Lemma smash_elim_simp_base_2 : 
  @smash_elim_simp X _ f _ _ Ha Hb (base_2 X) = Yb.
Proof.
  apply (@smash_comp_base_2 X (fun _ => Y) f Ya Yb).
Defined.


(*
Lemma smash_elim_simp_contract_1 :
   forall a : A, 
  map (@smash_elim_simp X _ f _ _ Ha Hb) (contract_1 a) = 
*)

End smash_elim_simp_rules.



Definition smash (X : smash_data) : pt_type := {|
   carrier := (* smash_carrier *) X ; 
   point := smash_pair X (point A) (point B) 
|}.


(** a path from (a, b0) to (a0,b0)  *)

Definition edge_connected_1 (X : smash_data) (a : A) :
  smash_pair _ a (point B) = smash_pair X (point A)(point B).
apply (concat (y:=base_1 X)).
apply (contract_1 X a).
apply (! contract_1 X _).
Defined.

Lemma edge_connected_1_refl (X : smash_data) :
   edge_connected_1 X (point A) = idpath.
Proof.
  unfold edge_connected_1.
  apply opposite_right_inverse.
Qed.

Definition edge_connected_2 (X : smash_data) (b : B) :
  smash_pair _ (point A) b = smash_pair X (point A)(point B).
apply (concat (y:=base_2 X)).
apply (contract_2 X _ ).
apply (! contract_2 _ _ ).
Defined.

Lemma edge_connected_2_refl (X : smash_data) :
   edge_connected_2 X (point B) = idpath.
Proof.
  unfold edge_connected_2.
  apply opposite_right_inverse.
Qed.


End smash_product.

Module Import smash_notation.

Notation "< a , b >" := (smash_pair _ a b) 
 (at level 40, B at next level, left associativity).

End smash_notation.

Section smash_product_functorial.

Variables A B C D : pt_type.

Variable f : A .-> C.
Variable g : B .-> D.

Variable AB : smash_data A B.
Variable CD : smash_data C D.

Definition smashf_carrier : smash AB -> smash CD.
apply (@smash_elim_simp _ _ AB (smash CD)
        (fun a b => smash_pair _ (pr1 f a) (pr1 g b) )
        (base_1 CD)
        (base_2 CD)
).
- intro a.
(*  rewrite (pr2 g). *)
  pathvia (smash_pair CD (pr1 f a)(point D)).
  apply (map _ (pr2 g)).
  apply (contract_1).
- intro b.
  rewrite (pr2 f). 
(*  pathvia (smash_pair CD (point C)(pr1 g b)). *)
  apply contract_2.
Defined.

Definition smashf : smash AB .-> smash CD.
exists smashf_carrier.
unfold smashf_carrier.
change (point (smash AB)) with 
     (smash_pair AB (point A) (point B)).
rewrite smash_elim_simp_pair.
change (point (smash CD)) with
     (smash_pair CD (point C) (point D)).
pathvia (smash_pair CD (pr1 f (point A)) (point D)).
apply (map _ (pr2 g)).
rewrite (pr2 f).
reflexivity.
Defined.

(* need functorial properties *)

End smash_product_functorial.


