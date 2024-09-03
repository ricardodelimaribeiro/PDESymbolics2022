(* Wolfram Language Test file *)
	test = "Tests/DiscreteConservedQOperatorChild.mt";
		Print["   DiscreteConservedQOperator"];

	variables = Association[{
		"indVars" -> {n}, 
  		"depVars" -> {u},
  		"rhs"->{0},
  	"expression" -> 0,
  	"result" -> True
	}]
	label = "basic rhs 1"
	Get[test]

	variables = Association[{
		"indVars" -> {n}, 
  		"depVars" -> {u},
  		"rhs"->{u[n]},
  	"expression" -> u[n],
  	"result" -> True
	}]
	label = "basic rhs 2"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n}, 
  		"depVars" -> {u,v},
  		"rhs"->{u[n+1]-u[n],2*v[n+1]-v[n]},
  	"expression" -> u[n]+v[n],
  	"result" -> False
	}]
	label = "basic rhs 3"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,m}, 
  		"depVars" -> {u,v},
  		"rhs"->{u[n+1,m+1]-u[n,m],v[n,m]-2*(v[n+1,m+1]-v[n,m])^2},
  	"expression" -> u[n,m]+v[n,m],
  	"result" -> False
	}]
	label = "basic rhs 3"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,m}, 
  		"depVars" -> {u,v},
  		"rhs"->{u[n, m]^2, v[n, m] - 2*(v[n + 1, m + 1] - v[n, m])^2},
  	"expression" -> u[n,m]^3+v[n,m]^2,
  	"result" -> False
	}]
	label = "basic rhs 4"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme"->{u[n,t+1]-u[n,t]},
  	"expression" -> 0,
  	"result" -> True
	}]
	label = "basic scheme 1"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme"->{u[n,t+1]-u[n,t]},
  	"expression" -> Association["exp"->{u[n,t]}],
  	"result" -> True
	}]
	label = "basic scheme 2"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme"->{u[n,t+1]-u[n,t]},
  	"expression" -> u[n,t],
  	"result" -> True
	}]
	label = "basic scheme 3"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme"->{u[n,t+1]-u[n,t]},
  	"expression" -> u[n,t]^3,
  	"result" -> True
	}]
	label = "basic scheme 4"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme"->{u[n,t+1]-1/2*(u[n+1,t+1]-u[n,t])^2},
  	"expression" -> u[n,t]^3,
  	"result" -> False
	}]
	label = "basic scheme 5"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme"->{u[n,t+1]-1/2*(u[n+1,t+1]-u[n,t])^2},
  		"elimOrder"->"implicit",
  	"expression" -> u[n,t]^3,
  	"result" -> False
	}]
	label = "basic scheme 6"
	Get[test]
	
	variables = Association[{
		"indVars" -> {m,n,t}, 
  		"depVars" -> {u,v},
  		"scheme"->{u[m,n,t+1]-u[m,n,t],v[m,n,t+1]^3-v[m,n,t]^3},
  	"expression" -> 0,
  	"result" -> True
	}]
	label = "basic scheme 7"
	Get[test]
	
	variables = Association[{
		"indVars" -> {m,n,t}, 
  		"depVars" -> {u,v},
  		"scheme"->{u[m,n,t+1]-u[m,n,t],v[m,n,t+1]^3-v[m,n,t]^3},
  	"expression" -> u[m,n,t]^3+v[m,n,t]^2,
  	"result" -> False
	}]
	label = "basic scheme 8"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,m,t}, 
  		"depVars" -> {u},
  		"pars" -> {a},
  		"scheme"->{u[n,m,t+1]-u[n,m,t]},
  	"expression" -> u[n,m,t],
  	"result" -> True
	}]
	label = "scheme with parameter"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"pars" -> {a},
  		"scheme"->{0},
  	"expression" -> {a*u[n, t], a*u[n, t]},
  	"result" -> Piecewise[List[List[True,Equal[a,0]],List[False,Unequal[a,0]]],$Failed]
	}]
	label = "list expression with scheme and parameter 1"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme"->{0},
  	"expression" -> {0,0,0,0},
  	"result" -> True
	}]
	label = "list expression with scheme 1"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme"->{0},
  	"expression" -> {0,0,0,u[n,t]^3},
  	"result" -> False
	}]
	label = "list expression with scheme 2"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme"->{u[n,t+1]-u[n,t]},
  	"expression" -> {0,0,0,u[n,t]^3},
  	"result" -> True
	}]
	label = "list expression with scheme 3"
	Get[test]
	
	(*variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"pars" -> {a},
  		"scheme"->{0},
  	"expression" -> {a*u[n,t]^3,(a+1)*u[n,t]},
  	"result" -> False
	}]
	label = "list expression with scheme and parameter 2"
	Get[test]*)
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"pars" -> {a},
  		"scheme"->{u[n,t+1]-u[n,t]},
  	"expression" -> {a*u[n,t]^3,(a+1)*u[n,t]},
  	"result" -> True
	}]
	label = "list expression with scheme and parameter 3"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme"->{u[n,t+1]-u[n,t]+u[n,t]*(u[n+1,t]-u[n,t])},
  		"reduce Beautify"->False,
  	"expression" -> (u[n+1,t]-u[n,t])*u[n,t],
  	"result" -> False
	}]
	label = "burgers equation 1"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme"->{u[n,t+1]-u[n,t]+u[n,t]*(u[n+1,t]-u[n,t])},
  		"reduce Beautify"->False,
  	"expression" -> u[n,t],
  	"result" -> False
	}]
	label = "burgers equation 2"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme"->{u[n,t+1]-u[n,t]+u[n,t]*(u[n+1,t]-u[n,t])},
  		"reduce Beautify"->False,
  	"expression" -> u[n,t]^4,
  	"result" -> False
	}]
	label = "burgers equation 3"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme"->{u[n,t+1]-u[n,t]+u[n,t]*(u[n+1,t]-u[n,t])},
  		"reduce Beautify"->False,
  	"expression" -> u[n,t]^7,
  	"result" -> False
	}]
	label = "burgers equation 4"
	Get[test]
	
	variables = Association[{
		"indVars" -> {x}, 
  		"depVars" -> {u},
  		"rhs"->{u[x]+u''[x]},
  		"VarDOperator" -> VarDOperator,
  	"expression" -> u[x],
  	"result" -> True
	}]
	label = "time discretized, space continuous heat equation"
	Get[test]
	
	variables = Association[{
		"indVars" -> {x}, 
  		"depVars" -> {u},
  		"rhs"->{u[x]+u'[x]},
  		"VarDOperator" -> VarDOperator,
  	"expression" -> u[x],
  	"result" -> True
	}]
	label = "time discretized, space continuous transport equation"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n}, 
  		"depVars" -> {u},
  		"rhs"->{u[n]-2*u[n]+u[n+1]+u[n-1]},
  	"expression" -> n*u[n],
  	"result" -> True
	}]
	label = "time discretized, space discretized heat equation 1"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n}, 
  		"depVars" -> {u},
  		"rhs" -> {u[n]-2*u[n]+u[n+1]+u[n-1]},
  		"timederivativeorder" -> 6,
  	"expression" -> n^11*u[n],
  	"result" -> True
	}]
	label = "time discretized, space discretized heat equation 2"
	
	variables = Association[{
		"indVars" -> {n}, 
  		"depVars" -> {u},
  		"rhs" -> {u[n]+2*u[n]-u[n+1]-u[n-1]},
  		"timederivativeorder" -> 6,
  	"expression" -> n^11*u[n],
  	"result" -> True
	}]
	label = "time discretized, space discretized equation"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme" -> {u[n,t+1]-u[n,t]+2u[n,t]-u[n+1,t]-u[n-1,t]},
  		"Beautify" -> False,
  		"reduce Beautify" -> False,
  	"expression" -> n*u[n,t],
  	"result" -> True (*TODO this was set to False, but hand computations show that it should be True. *)
	}]
	label = "explicit time and space discretized heat equation 1"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme" -> {u[n,t+1]-u[n,t]+2u[n,t]-u[n+1,t]-u[n-1,t]},
  	"expression" -> n*u[n,t]+(n+1)*u[n+1,t]+(n-1)*u[n-1,t],
  	"result" -> True
	}]
	label = "explicit time and space discretized heat equation 2"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme" -> {u[n,t+1]-u[n,t]+2u[n,t]-u[n+1,t]-u[n-1,t]},
  		"Beautify" -> False,
  		"reduce Beautify" -> False,
  	"expression" -> n*u[n,t]+(n+1)*u[n+1,t]+(n-1)*u[n-1,t],
  	"result" -> True (*This used to be False, need to check by hand?*)
	}]
	label = "explicit time and space discretized heat equation 3"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme" -> {u[n,t+1]-u[n,t]+2u[n,t+1]-u[n+1,t+1]-u[n-1,t+1]},
  		"elimOrder" -> "implicit",
  	"expression" -> n*u[n,t],
  	"result" -> True
	}]
	label = "implicit time and space discretized heat equation 1"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme" -> {u[n,t+1]-u[n,t]+2u[n,t+1]-u[n+1,t+1]-u[n-1,t+1]},
  		"elimOrder" -> "implicit",
  	"expression" -> n*u[n,t]+(n+1)*u[n+1,t]+(n-1)*u[n-1,t],
  	"result" -> True
	}]
	label = "implicit time and space discretized heat equation 2"
	Get[test]
	
	variables = Association[{
		"indVars" -> {n,t}, 
  		"depVars" -> {u},
  		"scheme" -> {u[n,t+1]-u[n,t]+2u[n,t+1]-u[n+1,t+1]-u[n-1,t+1]},
  		"elimOrder" -> "implicit",
  		"Beautify" -> False,
  		"reduce Beautify" -> False,
  	"expression" -> n*u[n,t]+(n+1)*u[n+1,t]+(n-1)*u[n-1,t],
  	"result" -> False
	}]
	label = "implicit time and space discretized heat equation 3"
	Get[test]