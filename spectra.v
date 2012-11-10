Require Import loop_spaces.
Require Import pointed_spaces.

Import pointed_spaces.pt_map_notation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record spectrum : Type := {
  spectrum_type :> nat -> pt_type ;
  spectrum_maps : forall n : nat,
       spectrum_type n .-> loop_space (spectrum_type (S n))
}.

Check (fun X : spectrum => X 2).

Section maps_of_spectra.

Variables X Y : spectrum.

Record spectrum_map := {
  spectrum_map_carrier : forall n, X n .-> Y n ;
  spectrum_map_commute : forall n,
    pt_map_compose 
        (spectrum_maps X n) 
        (loop_space_map (spectrum_map_carrier (S n) )) =
    pt_map_compose (spectrum_map_carrier _ ) (spectrum_maps Y _ )
}.

End maps_of_spectra.







