
Require Import HoTT.Homotopy.
Require Import pointed_spaces.

Set Implicit Arguments.
Unset Strict Implicit.


Section smash_product.

Variables A B : pt_type.



Reserved Notation "< A , B >"
 (at level 40, B at next level, left associativity).

Check @map_dep.
Check @map. About map.
Record smash_data : Type := {
  smash_carrier : Type ;
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
      map_dep (smash_elim d_contract_1 d_contract_2)(contract_1 a) = 
          map (transport (contract_1 a))
       ( smash_comp_base_1 (d_contract_1) d_contract_2 )
              @ d_contract_1 a @ 
                ! smash_comp_base_1 (d_contract_1) d_contract_2 

}.




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
