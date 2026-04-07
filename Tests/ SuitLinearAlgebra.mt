(* Wolfram Language Test file *)
If[
	Length[Names["PDESymbolics2022`VarDOperator"]] == 0,
	Get[FileNameJoin[{DirectoryName[$TestFileName], "..", "PDESymbolics2022", "PDESymbolics2022.m"}]]
];
		Print["LinearAlgebra"];

TestSuite[
	{
		"GaussianEliminationOperator.mt"
		,
		"EqualToZeroOperator.mt"
		,
		"ImprovedHomogeneousSolveAlwaysOperator.mt"
		,
		"MonomialDependenceOperator.mt"
		,
		"ParametricRefineOperator.mt"
		,
		"BasisOperator.mt"
		,
		"GenericLinearCombinationOperator.mt"
		,
		"MatrixInverseOperator.mt"

	}]
