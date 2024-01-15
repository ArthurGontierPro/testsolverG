
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
idstore = []                                # store the id constraints in a "reasonable" way
idctr = nboolctr
nboolctr = 2*ubx+ubv+ubv*sum([length(i) for i in Apatt])
function strat(x)                           # dumb strat to get next var to fix
    while x<=ubx if length(vars[x])==1 x+=1 else return x end end 
    return ubx+1
end

function bb(x,path,f)
    global vars,awake
    save = deepcopy((vars,awake))           # make a save of state
    if !filter(f) return false end           # call filtering
    x = strat(x)
    if x>ubx return true end                # all vars have values
    tmpvar = deepcopy(vars[x])
    push!(path,(0,0))
    for v in tmpvar                         # try to fix all values
        println(" try ",x,"=",v)
        vars[x] = Set([v])
        awake[x] = true
        path[end] = (x,v)
        if !bb(x,path,f)                    # recurcive call fo fix next var
            writerup(path,f)
            vars[x] = copy(tmpvar)
        else return true end                # we find a solution with this val
    end
    pop!(path)
    awake[x] = false
    vars,awake = save                       # revert state if filter fails
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
function filterneq(x,v)                     # filter overlaping nodes
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
function filtercard(x,v)                    # filter the node cardinal
    # println("   #",x," <= #",v)
    xn = Apatt[x]                           # get neighbors in pattern
    vn = Agraph[v]                          # get neighbors in graph
    return length(xn)<=length(vn)
end
function writepolcard(x,v,f)
    global idctr+=1
    write(f,string("p ",idstore[4][x][v][1]," "))
    for i in idstore[4][x][v][2:end]
        write(f,string(i," + "))
    end
    for n in Agraph[v]
        write(f,string(idstore[3][n]," + "))
    end
    write(f,string("0\n"))
    write(f,string("j ",idctr," 1 ~x",x,"_",v," >= 1 ;\n"))
    global idctr+=1
end
function filter(f)
    print(" filtering ")
    while any(x->x,awake)
        x = findfirst(x->x,awake)
        if length(vars[x]) == 1
            v = first(vars[x])
            if !filtercard(x,v)             # call filtering algorithms
                println("failed")
                writepolcard(x,v,f)
                return false 
            end
            if !filterneq(x,v)              # call filtering algorithms
                println("failed")
                return false 
            end
            if !filterimp(x,v)              # call filtering algorithms
                println("failed")
                return false 
            end
        end
        awake[x] = false
    end
    println("passed")
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
function writerup(path,f)
    global idctr+=1
    write(f,string("u"))
    for (x,v) in path
        write(f,string(" 1 ~x",x,"_",v))        
    end
    write(f,string(" >= 1 ;\n"))
end
function printrup(path)
    for (x,v) in path
        print(" 1 ~x",x,"_",v)
    end
    println(" >= 1 ;")
end
function writeopb()
    open(string(path,"test.opb"),"w") do f
        write(f,string("* #variable= ",ubx," #constraint= ",nboolctr,"\n"))
        for x in rx
            for v in rv
                write(f,string(" 1 x",x,"_",v))
            end
            write(f,string(" >= 1 ;\n"))
            for v in rv
                write(f,string(" -1 x",x,"_",v))
            end
            write(f,string(" >= -1 ;\n"))
        end
        push!(idstore,[i for i in 1:ubx],[i+ubx for i in 1:ubx])
        nid = 2ubx
        for v in rv
            for x in rx
                write(f,string(" -1 x",x,"_",v))
            end
            write(f,string(" >= -1 ;\n"))
        end
        push!(idstore,[i+nid for i in 1:ubv])
        nid+= ubv
        push!(idstore,[[[] for v in rv] for i in rx])
        for x in rx, xx in Apatt[x], v in rv
            write(f,string(" 1 ~x",x,"_",v))
            for vv in Agraph[v]
                write(f,string(" 1 x",xx,"_",vv))
            end
            write(f,string(" >= 1 ;\n"))
            nid+= 1
            push!(idstore[4][x][v],nid)
        end
    end
end

writeopb()
path = "\\\\wsl.localhost\\Ubuntu\\home\\arthur_gla\\veriPB\\testsolver\\"
println("==========================")
open(string(path,"test.pbp"),"w") do f
    write(f,string("pseudo-Boolean proof version 1.0\n"))
    write(f,string("f ",nboolctr,"\n"))
    if bb(lbx,[],f) 
        println("\n Yay a solutions !")
        for x in rx
            println("    X",x,"=", first(vars[x]))
        end
    else
        println("\n Oh nooo, No solutions")
        write(f,string("u >= 1 ;\n"))
        write(f,string("c ",idctr+1))
    end
end













#= 
veripb --trace --useColor test.opb test.pbp
restart RELP  alt j alt r
union ∪
intersect ∩
setdiff
symdiff rend les elements uniques
issubset ⊆⊇
i belive it matters
=#
