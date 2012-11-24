Set Implicit Arguments.
Unset Strict Implicit.

Require Import HoTT.Homotopy.
Require Import tactics.

Lemma map_twovar_nondep {A : Type} {P : Type} {B : Type} 
   {x y : A} {a : P } {b : P }
  (f : forall x : A, P  -> B) (p : x = y) (q :  a = b) :
  f x a = f y b.
Proof.
  induction p.
  simpl in q.
  induction q.
  apply idpath.
Defined.

Lemma map_twovar_2eq_nondep {A : Type} {P : Type} {B : Type} 
   {x y : A} {a : P } 
  (f : forall x : A, P  -> B) (p : x = y) :
  f x a = f y a.
Proof.
  induction p.
  apply idpath.
Defined.