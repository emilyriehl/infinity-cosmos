import InfinityCosmos.ForMathlib.InfinityCosmos.Isofibrations
import Lean

open CategoryTheory
open InfinityCosmos
open Lean Elab Command

universe u v

variable {K : Type u} [Category.{v} K] [InfinityCosmos K]
variable {A B C : K}

run_cmd
  let required := #[
    `SSet.coherentIso.lift,
    `SSet.Homotopy.trans,
    `SSet.Homotopy.symm,
    `SSet.Equiv.comp,
    `SSet.Equiv.of_comp_left,
    `SSet.Equiv.of_comp_right,
    `QCat.Equiv.comp,
    `InfinityCosmos.Equivalence.comp,
    `InfinityCosmos.Equivalence.of_comp_left,
    `InfinityCosmos.Equivalence.of_comp_right,
    `InfinityCosmos.coherentIsoEndpointPair_isIsofibration,
    `InfinityCosmos.brownFactorizationRight_isIsofibration,
    `InfinityCosmos.brownFactorizationSection_equivalence,
    `InfinityCosmos.brownFactorization_equivalence_iff_right_trivialFibration]
  let mut missing : Array Name := #[]
  for name in required do
    unless (← getEnv).contains name do
      missing := missing.push name
  unless missing.isEmpty do
    throwError "missing declarations: {missing}"

#check brownFactorizationRight_isIsofibration
#check brownFactorizationSection_equivalence
#check brownFactorization_equivalence_iff_right_trivialFibration

#print axioms SSet.coherentIso.lift
#print axioms SSet.Homotopy.trans
#print axioms SSet.Homotopy.symm
#print axioms SSet.Equiv.comp
#print axioms SSet.Equiv.of_comp_left
#print axioms SSet.Equiv.of_comp_right
#print axioms QCat.Equiv.comp
#print axioms InfinityCosmos.Equivalence.comp
#print axioms InfinityCosmos.Equivalence.of_comp_left
#print axioms InfinityCosmos.Equivalence.of_comp_right
#print axioms InfinityCosmos.coherentIsoEndpointPair_isIsofibration
#print axioms brownFactorizationRight_isIsofibration
#print axioms brownFactorizationSection_equivalence
#print axioms brownFactorization_equivalence_iff_right_trivialFibration
