(* Wolfram Language Test file *)
	test = "Tests/TemplateChild.mt";
		Print["   Template"];


label = "VarDOperator_variational derivative"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> VarDOperator, 
  	"expression" -> u[x]^2,
  	"result" -> {2 u[x]}
]
Get[test]

label = "FindIntegratingFactorBasisOperator_"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"indVars" -> {x, t}
		],
	"operator" -> FindIntegratingFactorBasisOperator,
	"expression"(*problem*) -> Association[
   "expression" -> {D[u[x, t], t] - D[u[x, t], x]},
   "monomials" -> Association["degree" -> 1, "derivatives" -> 2]],
   "result" -> {{1}, {u[x, t]}, {Derivative[0, 2][u][x, t]}, {Derivative[1, 1][u][x, t]}, {Derivative[2, 0][u][x, t]}}
]
Get[test]