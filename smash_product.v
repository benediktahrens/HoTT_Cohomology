
Set Implicit Arguments.
Unset Strict Implicit.

Require Import HoTT.Homotopy.
Require Import pointed_spaces.

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
  rewrite  (Ha a).
  apply trans_trivial.
  intro b.
  rewrite (Hb b).
  apply trans_trivial.
Defined.


Definition smash (X : smash_data) : pt_type := {|
   carrier := smash_carrier X ; 
   point := smash_pair X (point A) (point B) 
|}.


Definition smash_pr1_map (X : smash_data) : smash X -> A.
Proof.
  apply (smash_elim_simp  
                    (f := fun a _ => a)
                    (Ya := point A)
                    (Yb := point A)).
  
  intro a.
  Check (contract_1 X a).
  rewrite (contract_1 X).
  simpl.
   


(*

Record smash_data : Type := {
  smash_carrier : Type ;
  smash_pair : forall a : A , forall b : B, smash_carrier ;
  contr_1 : forall a : A, 
     smash_pair a (point B) = smash_pair (point A) (point B) ;
  contr_2 : forall b : B, 
     smash_pair (point A) b = smash_pair (point A) (point B) ;
  smash_rec : forall (P : smash_carrier -> Type) 
     (d : forall (a : A) (b : B), P (smash_pair a b))
     (H_1 : forall a : A, 
       transport (contr_1 a) (d a (point B)) = 
             d (point A) (point B)) 
     (H_2 : forall b : B, 
       transport (contr_2 b) (d (point A) b) = 
             d (point A) (point B)) ,

       forall ab : smash_carrier, P ab  
   ;
  smash_comp_pair : forall (P : smash_carrier -> Type) 
     (d : forall (a : A) (b : B), P (smash_pair a b))
     (H_1 : forall a : A, 
       transport (contr_1 a) (d a (point B)) = 
             d (point A) (point B)) 
     (H_2 : forall b : B, 
       transport (contr_2 b) (d (point A) b) = 
             d (point A) (point B)) ,
     forall a : A, forall b : B,
     smash_rec  H_1 H_2 (smash_pair a b) =
           d a b
;
   smash_comp_contr_1 : forall (P : smash_carrier -> Type) 
     (d : forall (a : A) (b : B), P (smash_pair a b))
     (H_1 : forall a : A, 
       transport (contr_1 a) (d a (point B)) = 
             d (point A) (point B)) 
     (H_2 : forall b : B, 
       transport (contr_2 b) (d (point A) b) = 
             d (point A) (point B)) ,
     forall a : A,
     map_dep (smash_rect H_1 H_2 (smash_pair a (point B))) (contr_1 a) =
          map (transport (contr_1 a)) 
}.

Definition smash (d : smash_data) : pt_type :=
  {| carrier := smash_carrier d ; 
     point := smash_pair _ (point A) (point B) |}.

*)

End smash_product.
