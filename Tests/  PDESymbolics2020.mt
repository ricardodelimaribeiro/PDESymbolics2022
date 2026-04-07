(* Wolfram Language Test file *)

If[
	Length[Names["PDESymbolics2022`VarDOperator"]] == 0,
	Get[FileNameJoin[{DirectoryName[$TestFileName], "..", "PDESymbolics2022", "PDESymbolics2022.m"}]]
];

TestSuite[
	{
		" SuitVariationalCalculus.mt"
		,
		" SuitLinearAlgebra.mt"
		,
		" SuitBeautify.mt"
		,
		" SuitTimeDependentPDEs.mt"
		,
		" SuitDiscrete.mt"
		,
		" SuitCGS.mt"
	}]
