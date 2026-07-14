import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.FibrationConservative
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.RightFibration

open SSet

#print axioms SSet.rightHornInclusions
#print axioms SSet.rightFibrations
#print axioms SSet.RightFibration
#print axioms SSet.rightAnodyneExtensions
#print axioms SSet.rightFibrations_le_innerFibrations
#print axioms SSet.innerAnodyneExtensions_le_rightAnodyneExtensions
#print axioms SSet.fibrations_le_rightFibrations
#print axioms SSet.rightAnodyneExtensions_le

#print axioms SSet.leftFibrationDataOfLeftFibration
#print axioms SSet.rightFibrationDataOfRightFibration
#print axioms SSet.leftFibration_conservative
#print axioms SSet.rightFibration_conservative
#print axioms SSet.leftFibration_isofibration
#print axioms SSet.rightFibration_isofibration

open SSet

example {X S : SSet} {p : X ⟶ S} [LeftFibration p] : LeftFibrationData p := inferInstance
example {X S : SSet} {p : X ⟶ S} [RightFibration p] : RightFibrationData p := inferInstance
