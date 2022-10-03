(* Wolfram Language Test file *)
test = "Tests/BasisModNullLagrangiansOperatorChild.mt"
Print["   BasisModNullLagrangiansOperator"];

label = "$Failed"
variables = Association[
	"MonList" -> $Failed, 
	"result" -> $Failed
];
Get[ test ]


label = "Piecewise basis"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"pars" -> {a},
	"MonList" -> {u[x]^a, u[x]^2},
	"result" -> Piecewise[{
	{{u[x]^2}, a == 0 || a == 2}, 
	{{u[x]^2, u[x]^a}, (-2 + a) a != 0}},
	$Failed]
}];
Get[ test ]


label = "Conditional basis (facts), refine on"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"pars" -> {b},
	"facts" -> b<7,
	"MonList" -> {u[x],u'[x]^2, u[x]^b, u[x] u'[x]},
	"result" -> Piecewise[{{{u[x], Derivative[1][u][x]^2}, b == 0 || b == 1}, {{u[x], u[x]^b, Derivative[1][u][x]^2}, b < 0 || Inequality[0, Less, b, Less, 1] || Inequality[1, Less, b, Less, 7]}}, $Failed]
}];
Get[ test ]


label = "Conditional basis, refine off"
variables=Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"pars" -> {b},
	"facts" -> b<7,
	"refine" -> False,
	"MonList" -> {u[x],u'[x]^2, u[x]^b, u[x] u'[x]},
	"result" -> Piecewise[{{{u[x], Derivative[1][u][x]^2}, b == 0 || b == 1}, {{u[x], u[x]^b, Derivative[1][u][x]^2}, b < 0 || Inequality[0, Less, b, Less, 1] || Inequality[1, Less, b, Less, 7]}}, $Failed]
}];
Get[ test ]


label = "long (in time!) stuff!"
variables=Association[{
	"depVars"-> {u,v},
	"indVars"-> {x},
	"pars"-> {a,b},
	"refine"-> True,
	"MonList" -> {u[x],u'[x]^2, u[x]^b,u[x]^a v[x]^(b-3a+4),u'[x]^b u[x]^a, u'[x]^(2b)},
	"result" -> Piecewise[{{{u[x], u[x]^a*v[x]^(4 - 3*a + b), Derivative[1][u][x]^2}, (b == 0 && a == 0) || (b == 0 && a == 1) || (b == 0 && a == 4/3) || b == 1}, 
		{{u[x], u[x]^b, u[x]^a*v[x]^(4 - 3*a + b), Derivative[1][u][x]^2, u[x]^a*Derivative[1][u][x]^b, Derivative[1][u][x]^(2*b)}, (-2 + a)*(-1 + a)*a*(-1 + b)*b*(-1 + 2*b) != 0 || (-1 + a)*a*(-2 + b)*(-1 + b)*b*(-1 + 2*b) != 0 || (-2 + a)*a*(-1 + b)*b*(1 + b)*(-1 + 2*b) != 0 || a*(-2 + b)*(-1 + b)*b*(1 + b)*(-1 + 2*b) != 0 || (-1 + a)*(-2 + b)*(-1 + b)*b*(4 + b)*(-1 + 2*b) != 0 || (-2 + b)*(-1 + b)*b*(1 + b)*(4 + b)*(-1 + 2*b) != 0}, 
		{{u[x], u[x]^b, Derivative[1][u][x]^2, u[x]^a*Derivative[1][u][x]^b, Derivative[1][u][x]^(2*b)}, (b == -4 && a == 0) || (b == -1 && a == 1) || (b == 2 && a == 2)}, 
		{{u[x], u[x]^b, u[x]^a*v[x]^(4 - 3*a + b), Derivative[1][u][x]^2, Derivative[1][u][x]^(2*b)}, a == 0 && b == 2}, 
		{{u[x], u[x]^b, u[x]^a*v[x]^(4 - 3*a + b), Derivative[1][u][x]^2, u[x]^a*Derivative[1][u][x]^b}, b == 1/2}, 
		{{u[x], u[x]^a*v[x]^(4 - 3*a + b), Derivative[1][u][x]^2, u[x]^a*Derivative[1][u][x]^b}, (-1 + a)*a*(-4 + 3*a) != 0 && b == 0}}, 
		$Failed]
}];
(*Get[ test ]*)(*only uncomment this when you really need to!*)


label = "Unit basis"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"MonList" -> {u'[x]^2, Derivative[2][u][x]u[x]},
	"result" -> {Derivative[1][u][x]^2}
}];
Get[ test ]


label = "Unit basis more variables"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x, y},
	"MonList" -> {0.0, Derivative[1, 0][u][x, y]^2, 9 Derivative[2, 0][u][x, y]u[x, y]},
	"result" -> {Derivative[1, 0][u][x ,y]^2}
}];
Get[ test ]


label = "works on official notebook"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"pars" -> {a},
	"MonList" -> {
  		u[x]^2,
  		u[x] u'[x],
  		u'[x]^a,
  		u[x] u''[x],
  		u[x] u'''[x]},
  	"result" -> Piecewise[{{{u[x]^2, Derivative[1][u][x]^a}, a == 2}, 
  		{{u[x]^2, Derivative[1][u][x]^a, u[x]*Derivative[2][u][x]}, 
  		(-2 + a)*(-1 + a)*a != 0}, 
  		{{u[x]^2, u[x]*Derivative[2][u][x]}, a == 0 || a == 1}}, 
  		$Failed]
}];
Get[ test ]


label = "Exponentials"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {t},
	"pars" -> {a},
	"MonList" -> {E^ u[t] u'''[t], E^ u[t] u''[t] u'[t]},
  	"result" -> {E^u[t]*Derivative[1][u][t]*Derivative[2][u][t]}
}];
Get[ test ]


label = "All Null Lagrangians"
variables = Association[{
	"depVars" -> {u,v},
	"indVars" -> {x,y},
	"pars" -> {a},
	"MonList" -> {0, D[u[x, y], x],
		v[x, y] Derivative[0, 1][u][x, y] +
		u[x, y] Derivative[0, 1][v][x, y] },
  	"result" -> {}
}];
Get[ test ]


label = "No Null Lagrangians"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"pars" -> {a},
	"MonList" -> {u[x] Derivative[1][u][x] u'''[x]^4, Derivative[1][u][x]^2 u'''[x]^4},
  	"result" -> {u[x]*Derivative[1][u][x]*Derivative[3][u][x]^4, Derivative[1][u][x]^2*Derivative[3][u][x]^4}
}];
Get[ test ]


label = "m, not u"
variables = Association[{
	"depVars" -> {m},
	"indVars" -> {x},
	"pars" -> {a},
	"MonList" -> {m'[x], m[x]^2, m[x]^2 + 3 m'[x], 1 },
  	"result" -> {m[x]^2}
}];
Get[ test ]


(*other variational derivatives: discrete*)
label = "discrete, shift by 1"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {n},
	"VarDOperator"->DVarDOperator,
	"MonList" -> {u[n], u[n+1]},
	"result" -> {u[n]}
}];
Get[ test ]


label = "discrete, shift when a == 1"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {n},
	"pars" -> {a},
	"VarDOperator" -> DVarDOperator,
	"MonList" -> {u[n], u[n + 1]^a},
	"result" -> Piecewise[{{{u[n]}, a == 0 || a == 1}, {{u[n], u[1 + n]^a}, (-1 + a)*a != 0}}, $Failed]
}];
Get[ test ]


label = "discrete, two parameters"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {n},
	"pars" -> {a, b},
	"VarDOperator" -> DVarDOperator,
	"MonList" -> {u[n], u[n + 1]^a - b  u[n]^a},
	"result" -> Piecewise[{{{u[n]}, a == 0 || a == 1 || b == 1}, {{u[n], -(b*u[n]^a) + u[1 + n]^a}, (-1 + a)*a != 0 && -1 + b != 0}}, $Failed]
}];
Get[ test ]

  
label = "generic function: V"
variables = Association[{
	"depVars" -> {u},
	"genFuns" -> {V},
	"indVars" -> {x},
	"pars" -> {a},
	"MonList" -> {V'[u[x]] u'[x], u[x]^2},
	"result" -> {u[x]^2}
}];
Get[ test ]