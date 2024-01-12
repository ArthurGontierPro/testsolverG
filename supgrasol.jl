
patt = [(1,2),(1,3),(1,4)]                  # Pattern to find infeasable
# patt = [(1,2),(2,3),(3,4)]                  # pattern to find feasable
graph = [(1,2),(2,3),(3,4),(4,1)]           # Graph to search 
lbx = 1 ; ubx = 4 ; rx = lbx:ubx
lbv = 1 ; ubv = 4 ; rv = lbv:ubv
dom = Set([i for i in rv])
vars = [copy(dom) for i in rx]              # variable array
awake = [false for i in rx]                 # awaked state = need to filter
function adjarr(g,ub)
    A = [[] for i in 1:ub]
    for (i,j) in g
        push!(A[i],j)
        push!(A[j],i)
    end
    return A
end
Apatt = adjarr(patt,ubx)                    # neighbors into pattern
Agraph = adjarr(graph,ubv)                  # neighbors into graph
function strat(x)                            # dumb strat to get next var to fix
    while x<=ubx if length(vars[x])==1 x+=1 else return x end end 
    return ubx+1
end

function bb(x,path)
    global vars,awake
    save = deepcopy((vars,awake))           # make a save of state
    if !filter() return false end           # call filtering
    x = strat(x)
    if x>ubx return true end                # all vars have values
    tmpvar = deepcopy(vars[x])
    push!(path,(0,0))
    for v in tmpvar                         # try to fix all values
        println(" try ",x,"=",v)
        vars[x] = Set([v])
        awake[x] = true
        path[end] = (x,v)
        if !bb(x,path)                      # recurcive call fo fix next var
            printrup(path)
            vars[x] = copy(tmpvar)
        else return true end                # we find a solution with this val
    end
    pop!(path)
    awake[x] = false
    vars,awake = save               # revert state if filter fails
    return false                            # no values are valid
end

function filterimp(x,v)                     # filter the neighborhoods values
    # println("   ",x," -> ",v)
    xn = Apatt[x]                           # get neighbors in pattern
    vn = Agraph[v]                          # get neighbors in graph
    for n in xn
        nb = length(vars[n])
        intersect!(vars[n],vn)              # filter values not in neighborhoods
        if nb>length(vars[n])               # the domain has been reduced
            awake[n] = true
            if length(vars[n]) == 0         # the domain is emptied = no sol
                return false
            end
        end
    end
    return true
end
function filterneq(x,v)
    # println("   neq  ",v)
    for n in rx
        if n!=x 
        nb = length(vars[n])
        setdiff!(vars[n],Set([v]))          # filter value v from other domains
        if nb>length(vars[n])               # the domain has been reduced
            awake[n] = true
            if length(vars[n]) == 0         # the domain is emptied = no sol
                return false
            end
        end
        end
    end
    return true
end

function filter()                           # call filtering algorithms
    global vars,awake
    printvars()
    print(" filtering ")
    while any(x->x,awake)
        x = findfirst(x->x,awake)
        if length(vars[x]) == 1
            if !filterneq(x,first(vars[x])) # call filtering algorithms
                println("failed")
                return false 
            end
            if !filterimp(x,first(vars[x])) # call filtering algorithms
                println("failed")
                return false 
            end
        end
        awake[x] = false
    end
    println("passed")
    printvars()
    return true
end

function printvars()
    println()
    for x in rx
        println(vars[x]," ",
        if awake[x] "Awaken " else "" end)
    end 
    println()
end

function printrup(path)
    for (x,v) in path
        print(" 1 ~x",x,"_",v)
    end
    println(" >= 1 ;")
end

println("==========================")
if bb(lbx,[]) 
    println("\n Yay a solutions !")
    for x in rx
        println("    X",x,"=", first(vars[x]))
    end
else
    println("\n Oh nooo, No solutions")
end

function writeopb()
    println("* #variable= ",ubx," #constraint= ",2*ubx+ubv+ubv*sum([length(i) for i in Apatt]))
    for x in rx
        for v in rv
            print(" 1 x",x,"_",v)
        end
        println(" >= 1 ;")
        for v in rv
            print(" -1 x",x,"_",v)
        end
        println(" >= -1 ;")
    end
    for v in rv
        for x in rx
            print(" -1 x",x,"_",v)
        end
        println(" >= -1 ;")
    end
    for x in rx, v in rv, xx in Apatt[x]
        print(" 1 ~x",x,"_",v)
        for vv in Agraph[v]
            print(" 1 x",xx,"_",vv)
        end
        println(" >= 1 ;")
    end
end

writeopb()












#= 
restart RELP  alt j alt r
union ∪
intersect ∩
setdiff
symdiff rend les elements uniques
issubset ⊆⊇
i belive it matters
=#
