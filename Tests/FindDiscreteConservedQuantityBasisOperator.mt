(* Wolfram Language Test file *)

test = "Tests/FindDiscreteConservedQuantityBasisOperatorChild.mt";
		Print["   FindDiscreteConservedQuantityBasisOperator"];

	variables = Association[{
		"indVars" -> {n}, 
  		"depVars" -> {u},
  		"rhs"->{u[n+1]},
  	"expression" -> Association["degree"->4,"generators"->{u[n],n}],
  	"result" -> {u[n],u[n]^2,u[n]^3,u[n]^4}
	}]
	label = "basic transport eq"
	Get[test]

	variables = Association[{
		"indVars" -> {n}, 
  		"depVars" -> {u},
  		"pars" -> {a},
  		"rhs"->{u[n] + a*(u[n - 1] - 2 u[n] + u[n + 1])},
  	"expression" -> Association["degree"->3,"generators"->{u[n],n}],
  	"result" -> Piecewise[List[List[List[u[n],Times[n,u[n]]],Or[Equal[a,1/2],Unequal[Times[2,a],0]]],List[List[u[n],Times[n,u[n]],Times[Power[n,2],u[n]],Power[u[n],2],Times[n,Power[u[n],2]],Power[u[n],3]],Equal[a,0]]],$Failed]
	}]
	label = "heat equation with parameter"
	Get[test]
	
	
