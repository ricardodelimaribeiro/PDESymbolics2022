(* Wolfram Language Test file *)
test = "Tests/DisintegrateOperatorChild.mt"
		Print["   DisintegrateOperator"];

label = "$Failed"
variables = Association[
	"expression" -> $Failed, 
	"result" -> $Failed
	];
Get[ test ]

label = "Standard example"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"expression" ->  u[x] u''''[x],
	"pars"->{},
	"generators"->{},
	"facts"->True,
	"result" -> 
	(1 + Subscript[, 1] - Subscript[, 2])*Derivative[2][u][x]^2 + Subscript[, 1]*Derivative[1][u][x]*Derivative[3][u][x] + Subscript[, 2]*u[x]*Derivative[4][u][x]
	(*(1 - Subscript[, 1] - Subscript[, 2])*Derivative[2][u][x]^2 - Subscript[, 1]*Derivative[1][u][x]*Derivative[3][u][x] + Subscript[, 2]*u[x]*Derivative[4][u][x]*)
}];
Get[ test ]

label = "Exponential"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"pars"->{},
	"generators"->{},
	"facts"->True,
	"depth" -> 1,
	"expression" ->  E^u[x] u''[x],
	"result" -> 
	E^u[x]*(-1 + Subscript[, 1] + Subscript[, 2])*Derivative[1][u][x]^2 + E^u[x]*Subscript[, 2]*u[x]*Derivative[1][u][x]^2 + E^u[x]*Subscript[, 1]*Derivative[2][u][x] + E^u[x]*Subscript[, 2]*u[x]*Derivative[2][u][x]
	(*-(E^u[x]*(1 - Subscript[, 1] - Subscript[, 2])*Derivative[1][u][x]^2) + E^u[x]*Subscript[, 1]*Derivative[2][u][x] + Subscript[, 2]*(E^u[x]*u[x]*Derivative[1][u][x]^2 + E^u[x]*u[x]*Derivative[2][u][x])*)
}];
Get[ test ]

label = "Piecewise"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"depth" -> 1,
	"pars" -> {a},
	"generators"->{},
	"expression" ->  Piecewise[{{u[x]^a u''''[x], a > 0}, {u''''[x], a == 0}}, $Failed],
	"result" -> 
	Piecewise[{{$Failed, a < 0}, {Subscript[\[FormalA], 1]*Derivative[4][u][x], a == 0}}, 
 (u[x]^(-3 + a)*(-2*a*Derivative[1][u][x]^4 + 3*a^2*Derivative[1][u][x]^4 - 
    a^3*Derivative[1][u][x]^4 - 2*Subscript[\[FormalA], 2]*Derivative[1][u][x]^4 + 
    a*Subscript[\[FormalA], 2]*Derivative[1][u][x]^4 - 2*Subscript[\[FormalA], 3]*
     Derivative[1][u][x]^4 + 3*a*Subscript[\[FormalA], 3]*Derivative[1][u][x]^4 - 
    a^2*Subscript[\[FormalA], 3]*Derivative[1][u][x]^4 + 2*a*Subscript[\[FormalA], 4]*
     Derivative[1][u][x]^4 - 3*a^2*Subscript[\[FormalA], 4]*Derivative[1][u][x]^4 + 
    a^3*Subscript[\[FormalA], 4]*Derivative[1][u][x]^4 + 3*Subscript[\[FormalA], 2]*u[x]*
     Derivative[1][u][x]^2*Derivative[2][u][x] + 3*a*u[x]^2*Derivative[2][u][x]^2 + 
    3*Subscript[\[FormalA], 3]*u[x]^2*Derivative[2][u][x]^2 - 3*a*Subscript[\[FormalA], 4]*u[x]^2*
     Derivative[2][u][x]^2 + 3*Subscript[\[FormalA], 3]*u[x]^2*Derivative[1][u][x]*
     Derivative[3][u][x] + 3*Subscript[\[FormalA], 4]*u[x]^3*Derivative[4][u][x]))/3]
     (*Piecewise[{{$Failed, a < 0}, {Subscript[, 1]*Derivative[4][u][x], a == 0}}, (-(a*u[x]^a*Derivative[1][u][x]^2*Derivative[2][u][x]) + a^2*u[x]^a*Derivative[1][u][x]^2*Derivative[2][u][x] + a*Subscript[, 2]*u[x]^a*Derivative[1][u][x]^2*Derivative[2][u][x] - a^2*Subscript[, 2]*u[x]^a*Derivative[1][u][x]^2*Derivative[2][u][x] + a*Subscript[, 3]*u[x]^a*Derivative[1][u][x]^2*Derivative[2][u][x] - a^2*Subscript[, 3]*u[x]^a*Derivative[1][u][x]^2*Derivative[2][u][x] + a*Subscript[, 4]*u[x]^a*Derivative[1][u][x]^2*Derivative[2][u][x] - a^2*Subscript[, 4]*u[x]^a*Derivative[1][u][x]^2*Derivative[2][u][x] + a*u[x]^(1 + a)*Derivative[2][u][x]^2 - a*Subscript[, 2]*u[x]^(1 + a)*Derivative[2][u][x]^2 - a*Subscript[, 3]*u[x]^(1 + a)*Derivative[2][u][x]^2 - a*Subscript[, 4]*u[x]^(1 + a)*Derivative[2][u][x]^2 - a*Subscript[, 2]*u[x]^(1 + a)*Derivative[1][u][x]*Derivative[3][u][x] - a*Subscript[, 4]*u[x]^(1 + a)*Derivative[1][u][x]*Derivative[3][u][x] + a^2*Subscript[, 4]*u[x]^(1 + a)*Derivative[1][u][x]*Derivative[3][u][x] + Subscript[, 3]*u[x]^(2 + a)*Derivative[4][u][x] + a*Subscript[, 4]*u[x]^(2 + a)*Derivative[4][u][x])/u[x]^2]*)
}];
Get[ test ]

label = "Two variables, two derivatives in x, (balance in x)"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x,y},
	"pars"->{},
	"generators"->{},
	"facts"->True,
	"intVars" -> {x},
	"expression" ->  u[x, y] D[u[x, y], {x, 2}],
	"result" -> (-1 + Subscript[, 1])*Derivative[1, 0][u][x, y]^2 + Subscript[, 1]*u[x, y]*Derivative[2, 0][u][x, y]
	(*-((1 - Subscript[, 1])*Derivative[1, 0][u][x, y]^2) + Subscript[, 1]*u[x, y]*Derivative[2, 0][u][x, y]*)
}];
Get[ test ]

label = "Two variables, two derivatives in y, (balance in x)"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x,y},
	"intVars" -> {x},
	"pars"->{},
	"generators"->{},
	"facts"->True,
	"expression" ->  u[x, y] D[u[x, y], {y, 2}],
	"result" -> 
	(-1 + Subscript[, 1])*Derivative[0, 1][u][x, y]^2 + Subscript[, 1]*u[x, y]*Derivative[0, 2][u][x, y]
	(*-((1 - Subscript[, 1])*Derivative[0, 1][u][x, y]^2) + Subscript[, 1]*u[x, y]*Derivative[0, 2][u][x, y]*)
	}];
Get[ test ]

label = "Two variables, two derivatives in x"
variables = Association[{
	"depVars" -> {u,v},
	"indVars" -> {x,y},
	"pars"->{},
	"generators"->{},
	"facts"->True,
	"expression" ->  u[x, y] D[v[x, y], {x, 2}],
	"result" -> 
	(-1 + Subscript[, 1] + Subscript[, 2])*Derivative[1, 0][u][x, y]*Derivative[1, 0][v][x, y] + Subscript[, 1]*v[x, y]*Derivative[2, 0][u][x, y] + Subscript[, 2]*u[x, y]*Derivative[2, 0][v][x, y]
	(*-((1 - Subscript[, 1] - Subscript[, 2])*Derivative[1, 0][u][x, y]*Derivative[1, 0][v][x, y]) + Subscript[, 1]*v[x, y]*Derivative[2, 0][u][x, y] + Subscript[, 2]*u[x, y]*Derivative[2, 0][v][x, y]*)
	}];
Get[ test ]

label = "Two variables, two derivatives in y"
variables = Association[{
	"depVars" -> {u,v},
	"indVars" -> {x,y},
	"pars"->{},
	"generators"->{},
	"facts"->True,
	"expression" ->  v[x, y] D[u[x, y], {y, 2}],
	"result" -> (-1 + Subscript[, 1] + Subscript[, 2])*Derivative[0, 1][u][x, y]*Derivative[0, 1][v][x, y] + Subscript[, 1]*v[x, y]*Derivative[0, 2][u][x, y] + Subscript[, 2]*u[x, y]*Derivative[0, 2][v][x, y]
	(*-((1 - Subscript[, 1] - Subscript[, 2])*Derivative[0, 1][u][x, y]*Derivative[0, 1][v][x, y]) + Subscript[, 1]*v[x, y]*Derivative[0, 2][u][x, y] + Subscript[, 2]*u[x, y]*Derivative[0, 2][v][x, y]*)
	}];
Get[ test ]

label = "Parameters without piecewise result."
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"pars" -> {a},
	"generators"->{},
	"facts"->True,
	"depth" -> 1,
	"expression" ->  u[x] u'[x]^a,
	"result" -> {}
	}];
Get[ test ]

   