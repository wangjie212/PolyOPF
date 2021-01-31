mutable struct mcpop_data
    n # the number of all variables
    nb # the number of binary variables
    m # the number of all constraints
    numeq # the number of equality constraints
    supp # the support data
    coe # the coefficient data
    dg # the degree vector of constraints
    basis # the bases
    rlorder # the relaxation order
    ksupp # the extending support at the k-th step
    cql # the number of cliques
    cliques # the cliques of variables
    cliquesize # the numbers of cliques
    J # constraints associated to each clique
    ncc # constraints associated to no clique
    sb # the sizes of different blocks
    numb # the numbers of different blocks
    blocks # the block structure
    cl # the numbers of blocks
    blocksize # the sizes of blocks
    solver # the SDP solver
    tol # the tolerance to certify global optimality
    flag # 0 if global optimality is certified; 1 otherwise
end

"""
    opt,sol,data = cs_tssos_first(pop, x, d; nb=0, numeq=0, foc=100, CS="MF", minimize=true,
    assign="first", TS="block", solver="Mosek", QUIET=false, solve=true, solution=false,
    MomentOne=true, tol=1e-4)

Compute the first step of the CS-TSSOS hierarchy for constrained polynomial optimization with
relaxation order `d`.

# Arguments
- `pop`: the vector of the objective function, inequality constraints, and equality constraints.
- `x`: the set of variables.
- `d`: the relaxation order of the moment-SOS hierarchy.
- `nb`: the number of binary variables in `x`.
- `numeq`: the number of equality constraints.
"""
function cs_tssos_first(pop, x, d; nb=0, numeq=0, foc=100, CS="MF", minimize=true, assign="first",
    TS="block", solver="Mosek", QUIET=false, solve=true, solution=false, MomentOne=true, tol=1e-4)
    n=length(x)
    m=length(pop)-1
    coe=Vector{Vector{Float64}}(undef, m+1)
    supp=Vector{Vector{Vector{UInt16}}}(undef, m+1)
    for k=1:m+1
        mon=monomials(pop[k])
        coe[k]=coefficients(pop[k])
        lm=length(mon)
        supp[k]=[UInt16[] for i=1:lm]
        for i=1:lm
            ind=mon[i].z .>0
            vars=mon[i].vars[ind]
            exp=mon[i].z[ind]
            for j=1:length(vars)
                l=ncbfind(x, n, vars[j])
                append!(supp[k][i], l*ones(UInt16, exp[j]))
            end
        end
    end
    dg=maxdegree.(pop[2:m+1])
    cliques,cql,cliquesize=clique_decomp(n,m,dg,supp,order=d,alg=CS,minimize=minimize)
    J,ncc=assign_constraint(m,supp,cliques,cql,cliquesize,assign=assign)
    rlorder=init_order(dg,J,cliquesize,cql,foc=foc,order=d)
    blocks,cl,blocksize,sb,numb,basis,status=get_cblocks_mix!(dg,J,rlorder,m,supp,cliques,cql,cliquesize,nb=nb,TS=TS)
    opt,ksupp,moment=blockcpop_mix(n,m,supp,coe,basis,cliques,cql,cliquesize,J,ncc,blocks,cl,blocksize,numeq=numeq,nb=nb,QUIET=QUIET,TS=TS,solver=solver,solve=solve,solution=solution,MomentOne=MomentOne)
    if solution==true
        sol,flag=approx_sol(opt, moment, n, cliques, cql, cliquesize, supp, coe, numeq=numeq, tol=tol)
    else
        sol=nothing
        flag=1
    end
    data=mcpop_data(n,nb,m,numeq,supp,coe,dg,basis,rlorder,ksupp,cql,cliques,cliquesize,J,ncc,sb,numb,blocks,cl,blocksize,solver,tol,flag)
    return opt,sol,data
end

"""
    opt,sol,data = cs_tssos_first(supp::Vector{Vector{Vector{UInt16}}}, coe::Vector{Vector{Float64}},
    n, d; numeq=0, nb=0, foc=100, CS="MF", minimize=true, assign="first", TS="block", QUIET=false,
    solver="Mosek", solve=true, solution=false, MomentOne=true, tol=1e-4)

Compute the first step of the CS-TSSOS hierarchy for constrained polynomial optimization with
relaxation order `d`. Here the polynomial optimization problem is defined by `supp` and `coe`,
corresponding to the supports and coeffients of `pop` respectively.

# Arguments
- `pop`: the vector of the objective function, inequality constraints, and equality constraints.
- `x`: the set of variables.
- `d`: the relaxation order of the moment-SOS hierarchy.
- `nb`: the number of binary variables in `x`.
- `numeq`: the number of equality constraints.
"""
function cs_tssos_first(supp::Vector{Vector{Vector{UInt16}}}, coe::Vector{Vector{Float64}}, n, d;
    numeq=0, nb=0, foc=100, CS="MF", minimize=true, assign="first", TS="block", QUIET=false,
    solver="Mosek", solve=true, solution=false, MomentOne=true, tol=1e-4)
    m=length(supp)-1
    dg=[maximum(length.(supp[i])) for i=2:m+1]
    cliques,cql,cliquesize=clique_decomp(n,m,dg,supp,order=d,alg=CS,minimize=minimize)
    J,ncc=assign_constraint(m,supp,cliques,cql,cliquesize,assign=assign)
    rlorder=init_order(dg,J,cliquesize,cql,foc=foc,order=d)
    blocks,cl,blocksize,sb,numb,basis,status=get_cblocks_mix!(dg,J,rlorder,m,supp,cliques,cql,cliquesize,nb=nb,TS=TS)
    opt,ksupp,moment=blockcpop_mix(n,m,supp,coe,basis,cliques,cql,cliquesize,J,ncc,blocks,cl,blocksize,numeq=numeq,nb=nb,QUIET=QUIET,TS=TS,solver=solver,solve=solve,solution=solution,MomentOne=MomentOne)
    if solution==true
        sol,flag=approx_sol(opt, moment, n, cliques, cql, cliquesize, supp, coe, numeq=numeq, tol=tol)
    else
        sol=nothing
        flag=1
    end
    data=mcpop_data(n,nb,m,numeq,supp,coe,dg,basis,rlorder,ksupp,cql,cliques,cliquesize,J,ncc,sb,numb,blocks,cl,blocksize,solver,tol,flag)
    return opt,sol,data
end

"""
    opt,sol,data = cs_tssos_higher!(data; TS="block", QUIET=false, solve=true,
    solution=false, MomentOne=false)

Compute higher steps of the CS-TSSOS hierarchy.
Return the optimum, the (near) optimal solution (if `solution=true`) and other data.
"""
function cs_tssos_higher!(data; TS="block", QUIET=false, solve=true, solution=false, MomentOne=false)
    n=data.n
    nb=data.nb
    m=data.m
    numeq=data.numeq
    supp=data.supp
    coe=data.coe
    dg=data.dg
    basis=data.basis
    rlorder=data.rlorder
    ksupp=data.ksupp
    cql=data.cql
    cliques=data.cliques
    cliquesize=data.cliquesize
    J=data.J
    ncc=data.ncc
    blocks=data.blocks
    cl=data.cl
    blocksize=data.blocksize
    sb=data.sb
    numb=data.numb
    solver=data.solver
    tol=data.tol
    blocks,cl,blocksize,sb,numb,basis,status=get_cblocks_mix!(dg,J,rlorder,m,supp,cliques,cql,cliquesize,tsupp=ksupp,basis=basis,blocks=blocks,cl=cl,blocksize=blocksize,sb=sb,numb=numb,nb=nb,TS=TS)
    opt=nothing
    sol=nothing
    if status==1
        opt,ksupp,moment=blockcpop_mix(n,m,supp,coe,basis,cliques,cql,cliquesize,J,ncc,blocks,cl,blocksize,numeq=numeq,nb=nb,QUIET=QUIET,solver=solver,solve=solve,solution=solution,MomentOne=MomentOne)
        if solution==true
            sol,data.flag=approx_sol(opt, moment, n, cliques, cql, cliquesize, supp, coe, numeq=numeq, tol=tol)
        end
        data.ksupp=ksupp
        data.blocks=blocks
        data.cl=cl
        data.blocksize=blocksize
        data.sb=sb
        data.numb=numb
    else
        println("No higher CS-TSSOS hierarchy!")
    end
    return opt,sol,data
end

function blockcpop_mix(n, m, supp::Vector{Vector{Vector{UInt16}}}, coe, basis, cliques, cql, cliquesize,
    J, ncc, blocks, cl, blocksize; numeq=0, nb=0, QUIET=false, TS="block", solver="Mosek", solve=true,
    solution=false, MomentOne=false)
    tsupp=Vector{UInt16}[]
    for i=1:cql, j=1:cl[i][1], k=1:blocksize[i][1][j], r=k:blocksize[i][1][j]
        @inbounds bi=sadd(basis[i][1][blocks[i][1][j][k]], basis[i][1][blocks[i][1][j][r]], nb=nb)
        push!(tsupp, bi)
    end
    if (MomentOne==true||solution==true)&&TS!=false
        ksupp=copy(tsupp)
    end
    for i=1:cql, (j, w) in enumerate(J[i])
        for l=1:cl[i][j+1], t=1:blocksize[i][j+1][l], r=t:blocksize[i][j+1][l], s=1:length(supp[w+1])
            ind1=blocks[i][j+1][l][t]
            ind2=blocks[i][j+1][l][r]
            @inbounds bi=sadd(sadd(basis[i][j+1][ind1], supp[w+1][s], nb=nb), basis[i][j+1][ind2], nb=nb)
            push!(tsupp, bi)
        end
    end
    for i ∈ ncc, j=1:length(supp[i+1])
        push!(tsupp, supp[i+1][j])
    end
    if (MomentOne==true||solution==true)&&TS!=false
        for i=1:cql, j=1:cliquesize[i]
            push!(tsupp, [cliques[i][j]])
            for k=j+1:cliquesize[i]
                push!(tsupp, [cliques[i][j];cliques[i][k]])
            end
        end
    end
    sort!(tsupp)
    unique!(tsupp)
    if (MomentOne==true||solution==true)&&TS!=false
        sort!(ksupp)
        unique!(ksupp)
    else
        ksupp=tsupp
    end
    objv=nothing
    if solve==true
        ltsupp=length(tsupp)
        if solver=="Mosek"
            model=Model(optimizer_with_attributes(Mosek.Optimizer))
        elseif solver=="SDPT3"
            model=Model(optimizer_with_attributes(SDPT3.Optimizer))
        else
            @error "The solver is currently not supported!"
            return nothing,nothing,nothing
        end
        set_optimizer_attribute(model, MOI.Silent(), QUIET)
        cons=[AffExpr(0) for i=1:ltsupp]
        for i=1:cql
            if (MomentOne==true||solution==true)&&TS!=false
                bs=cliquesize[i]+1
                pos=@variable(model, [1:bs, 1:bs], PSD)
                for t=1:bs, r=t:bs
                    if t==1&&r==1
                        bi=UInt16[]
                    elseif t==1&&r>1
                        bi=[cliques[i][r-1]]
                    else
                        bi=sadd(cliques[i][t-1], cliques[i][r-1], nb=nb)
                    end
                    Locb=bfind(tsupp, ltsupp, bi)
                    if t==r
                        @inbounds add_to_expression!(cons[Locb], pos[t,r])
                    else
                        @inbounds add_to_expression!(cons[Locb], 2, pos[t,r])
                    end
                end
            end
            for l=1:cl[i][1]
                @inbounds bs=blocksize[i][1][l]
                if bs==1
                    pos=@variable(model, lower_bound=0)
                    @inbounds bi=sadd(basis[i][1][blocks[i][1][l][1]], basis[i][1][blocks[i][1][l][1]], nb=nb)
                    Locb=bfind(tsupp,ltsupp,bi)
                    @inbounds add_to_expression!(cons[Locb], pos)
                else
                    pos=@variable(model, [1:bs, 1:bs], PSD)
                    for t=1:bs, r=t:bs
                        @inbounds ind1=blocks[i][1][l][t]
                        @inbounds ind2=blocks[i][1][l][r]
                        @inbounds bi=sadd(basis[i][1][ind1], basis[i][1][ind2], nb=nb)
                        Locb=bfind(tsupp,ltsupp,bi)
                        if t==r
                            @inbounds add_to_expression!(cons[Locb], pos[t,r])
                        else
                            @inbounds add_to_expression!(cons[Locb], 2, pos[t,r])
                        end
                    end
                end
            end
        end
        for i in ncc
            if i<=m-numeq
                pos=@variable(model, lower_bound=0)
            else
                pos=@variable(model)
            end
            for j=1:length(supp[i+1])
                Locb=bfind(tsupp,ltsupp,supp[i+1][j])
                @inbounds add_to_expression!(cons[Locb], coe[i+1][j], pos)
            end
        end
        for i=1:cql, (j, w) in enumerate(J[i]), l=1:cl[i][j+1]
            bs=blocksize[i][j+1][l]
            if bs==1
                if w<=m-numeq
                    pos=@variable(model, lower_bound=0)
                else
                    pos=@variable(model)
                end
                ind=blocks[i][j+1][l][1]
                for s=1:length(supp[w+1])
                    @inbounds bi=sadd(sadd(basis[i][j+1][ind], supp[w+1][s], nb=nb), basis[i][j+1][ind], nb=nb)
                    Locb=bfind(tsupp,ltsupp,bi)
                    @inbounds add_to_expression!(cons[Locb], coe[w+1][s], pos)
                end
            else
                if w<=m-numeq
                    pos=@variable(model, [1:bs, 1:bs], PSD)
                else
                    pos=@variable(model, [1:bs, 1:bs], Symmetric)
                end
                for t=1:bs, r=t:bs
                    ind1=blocks[i][j+1][l][t]
                    ind2=blocks[i][j+1][l][r]
                    for s=1:length(supp[w+1])
                        @inbounds bi=sadd(sadd(basis[i][j+1][ind1], supp[w+1][s], nb=nb), basis[i][j+1][ind2], nb=nb)
                        Locb=bfind(tsupp,ltsupp,bi)
                        if t==r
                            @inbounds add_to_expression!(cons[Locb], coe[w+1][s], pos[t,r])
                        else
                            @inbounds add_to_expression!(cons[Locb], 2*coe[w+1][s], pos[t,r])
                        end
                    end
                end
            end
        end
        bc=zeros(ltsupp)
        for i=1:length(supp[1])
            Locb=bfind(tsupp,ltsupp,supp[1][i])
            if Locb==0
               @error "The monomial basis is not enough!"
               return nothing,nothing,nothing
            else
               bc[Locb]=coe[1][i]
            end
        end
        @variable(model, lower)
        if solution==true
            cons[1]+=lower
            @constraint(model, con[i=1:ltsupp], cons[i]==bc[i])
        else
            @constraint(model, cons[2:end].==bc[2:end])
            @constraint(model, cons[1]+lower==bc[1])
        end
        @objective(model, Max, lower)
        optimize!(model)
        status=termination_status(model)
        objv = objective_value(model)
        if status!=MOI.OPTIMAL
           println("termination status: $status")
           status=primal_status(model)
           println("solution status: $status")
        end
        println("optimum = $objv")
        if solution==true
            measure=-dual.(con)
            moment=get_moment(measure,tsupp,cliques,cql,cliquesize,nb=nb)
        else
            moment=nothing
        end
    end
    return objv,ksupp,moment
end

function init_order(dg, J, cliquesize, cql; foc=100, order="min")
    rlorder=ones(Int,cql)
    if order=="min"
        for i=1:cql
            if !isempty(J[i])
                rlorder[i]=ceil(Int, maximum(dg[J[i]])/2)
            end
        end
    else
        for i=1:cql
            if cliquesize[i]<=foc
                rlorder[i]=order
            end
        end
    end
    return rlorder
end

function get_cblocks_mix!(dg, J, rlorder, m, supp::Vector{Vector{Vector{UInt16}}}, cliques, cql,
    cliquesize; tsupp=[], basis=[], blocks=[], cl=[], blocksize=[], sb=[], numb=[], TS="block",
    nb=0, merge=false)
    if isempty(tsupp)
        blocks=Vector{Vector{Vector{Vector{UInt16}}}}(undef, cql)
        cl=Vector{Vector{UInt16}}(undef, cql)
        blocksize=Vector{Vector{Vector{Int}}}(undef, cql)
        sb=Vector{Vector{UInt16}}(undef, cql)
        numb=Vector{Vector{UInt16}}(undef, cql)
        basis=Vector{Vector{Vector{Vector{UInt16}}}}(undef, cql)
        tsupp=copy(supp[1])
        for i=2:m+1, j=1:length(supp[i])
            push!(tsupp, supp[i][j])
        end
        sort!(tsupp)
        unique!(tsupp)
        flag=1
    else
        flag=0
    end
    status=ones(Int, cql)
    for i=1:cql
        lc=length(J[i])
        lt=length.(supp[J[i].+1])
        nvar=cliquesize[i]
        ind=[issubset(tsupp[j], cliques[i]) for j=1:length(tsupp)]
        fsupp=copy(tsupp[ind])
        if flag==1
            basis[i]=Vector{Vector{Vector{UInt16}}}(undef, lc+1)
            basis[i][1]=get_sbasis(cliques[i], rlorder[i], nb=nb)
            for j=1:length(basis[i][1])
                push!(fsupp, sadd(basis[i][1][j], basis[i][1][j], nb=nb))
            end
            sort!(fsupp)
            unique!(fsupp)
            for s=1:lc
                basis[i][s+1]=get_sbasis(cliques[i], rlorder[i]-ceil(Int, dg[J[i][s]]/2), nb=nb)
            end
            blocks[i]=Vector{Vector{Vector{UInt16}}}(undef, lc+1)
            cl[i]=Vector{UInt16}(undef, lc+1)
            blocksize[i]=Vector{Vector{Int}}(undef, lc+1)
            sb[i]=Vector{UInt16}(undef, lc+1)
            numb[i]=Vector{UInt16}(undef, lc+1)
            blocks[i],cl[i],blocksize[i],sb[i],numb[i],status[i]=get_cblocks!(lc,fsupp,supp[J[i].+1],lt,basis[i],TS=TS,nb=nb,QUIET=true,merge=merge)
        else
            blocks[i],cl[i],blocksize[i],sb[i],numb[i],status[i]=get_cblocks!(lc,fsupp,supp[J[i].+1],lt,basis[i],blocks=blocks[i],cl=cl[i],blocksize=blocksize[i],sb=sb[i],numb=numb[i],TS=TS,nb=nb,QUIET=true,merge=merge)
        end
    end
    return blocks,cl,blocksize,sb,numb,basis,maximum(status)
end

function get_cblocks!(m, tsupp, supp, lt, basis; blocks=[], cl=[], blocksize=[], sb=[], numb=[], nb=0,
    TS="block", QUIET=true, merge=false)
    if isempty(blocks)
        blocks=Vector{Vector{Vector{UInt16}}}(undef, m+1)
        blocksize=Vector{Vector{UInt16}}(undef, m+1)
        cl=Vector{UInt16}(undef, m+1)
    end
    if TS==false
        blocksize[1]=[size(basis[1],2)]
        blocks[1]=[[i for i=1:size(basis[1],2)]]
        cl[1]=1
        for k=1:m
            blocks[k+1]=[[i for i=1:size(basis[k+1],2)]]
            blocksize[k+1]=[size(basis[k+1],2)]
            cl[k+1]=1
        end
        status=1
        nsb=Int.(blocksize[1])
        nnumb=[1]
        if QUIET==false
            println("------------------------------------------------------")
            println("The sizes of PSD blocks:\n$nsb\n$nnumb")
            println("------------------------------------------------------")
        end
    else
        G=get_graph(tsupp, basis[1], nb=nb)
        if TS=="block"
            blocks[1]=connected_components(G)
            blocksize[1]=length.(blocks[1])
            cl[1]=length(blocksize[1])
        else
            blocks[1],cl[1],blocksize[1]=chordal_cliques!(G, method=TS, minimize=false)
            if merge==true
                blocks[1],cl[1],blocksize[1]=clique_merge!(blocks[1], cl[1], QUIET=true)
            end
        end
        nsb=Int.(unique(blocksize[1]))
        nnumb=[sum(blocksize[1].== i) for i in nsb]
        if isempty(sb)||nsb!=sb||nnumb!=numb
            status=1
            if QUIET==false
                println("------------------------------------------------------")
                println("The sizes of PSD blocks:\n$nsb\n$nnumb")
                println("------------------------------------------------------")
            end
            for k=1:m
                G=get_cgraph(tsupp,supp[k],lt[k],basis[k+1],nb=nb)
                if TS=="block"
                    blocks[k+1]=connected_components(G)
                    blocksize[k+1]=length.(blocks[k+1])
                    cl[k+1]=length(blocksize[k+1])
                else
                    blocks[k+1],cl[k+1],blocksize[k+1]=chordal_cliques!(G, method=TS, minimize=false)
                    if merge==true
                        blocks[k+1],cl[k+1],blocksize[k+1]=clique_merge!(blocks[k+1], cl[k+1], QUIET=true)
                    end
                end
            end
        else
            status=0
            if QUIET==false
               println("No higher TSSOS hierarchy!")
            end
        end
    end
    return blocks,cl,blocksize,nsb,nnumb,status
end

function assign_constraint(m, supp::Vector{Vector{Vector{UInt16}}}, cliques, cql, cliquesize; assign="first")
    J=[UInt32[] for i=1:cql]
    ncc=UInt32[]
    for i=2:m+1
        rind=copy(supp[i][1])
        for j=2:length(supp[i])
            append!(rind, supp[i][j])
        end
        unique!(rind)
        if assign=="first"
            ind=findfirst(k->issubset(rind, cliques[k]), 1:cql)
            if ind!=nothing
                push!(J[ind], i-1)
            else
                push!(ncc, i-1)
            end
        else
            temp=UInt32[]
            for j=1:cql
                if issubset(rind, cliques[j])
                    push!(temp, j)
                end
            end
            if !isempty(temp)
                if assign=="min"
                    push!(J[temp[argmin(cliquesize[temp])]], i-1)
                else
                    push!(J[temp[argmax(cliquesize[temp])]], i-1)
                end
            else
                push!(ncc, i-1)
            end
        end
    end
    return J,ncc
end

function get_sbasis(var, d; nb=0)
    n=length(var)
    lb=binomial(n+d,d)
    basis=Vector{Vector{UInt16}}(undef, lb)
    basis[1]=UInt16[]
    i=0
    t=1
    while i<d+1
        t+=1
        if length(basis[t-1])>=i&&basis[t-1][end-i+1:end]==var[n]*ones(UInt16, i)
           if i<d
               basis[t]=var[1]*ones(UInt16, i+1)
           end
           i+=1
        else
            j=bfind(var, n, basis[t-1][1])
            basis[t]=copy(basis[t-1])
            ind=findfirst(x->basis[t][x]!=var[j], 1:length(basis[t]))
            if ind==nothing
                ind=length(basis[t])+1
            end
            if j!=1
                basis[t][1:ind-2]=var[1]*ones(UInt16, ind-2)
            end
            basis[t][ind-1]=var[j+1]
        end
    end
    if nb>0
        ind=[!any([basis[i][j]==basis[i][j+1]&&basis[i][j]<=nb for j=1:length(basis[i])-1]) for i=1:lb]
        basis=basis[ind]
    end
    return basis
end

function get_graph(tsupp::Vector{Vector{UInt16}}, basis::Vector{Vector{UInt16}}; nb=0)
    lb=length(basis)
    G=SimpleGraph(lb)
    ltsupp=length(tsupp)
    for i = 1:lb, j = i+1:lb
        bi=sadd(basis[i], basis[j], nb=nb)
        if bfind(tsupp, ltsupp, bi)!=0
            add_edge!(G, i, j)
        end
    end
    return G
end

function get_cgraph(tsupp::Vector{Vector{UInt16}}, supp::Vector{Vector{UInt16}}, lt::Int,
    basis::Vector{Vector{UInt16}}; nb=0)
    lb=length(basis)
    ltsupp=length(tsupp)
    G=SimpleGraph(lb)
    for i = 1:lb, j = i+1:lb
        r=1
        while r<=lt
            bi=sadd(sadd(basis[i], supp[r], nb=nb), basis[j], nb=nb)
            if bfind(tsupp,ltsupp,bi)!=0
               break
            else
                r+=1
            end
        end
        if r<=lt
            add_edge!(G, i, j)
        end
    end
    return G
end

function clique_decomp(n, m, dg, supp::Vector{Vector{Vector{UInt16}}}; order="min", alg="MF", minimize=false)
    if alg==false
        cliques=[UInt16[i for i=1:n]]
        cql=1
        cliquesize=[n]
    else
        G=SimpleGraph(n)
        for i=1:m+1
            if order=="min"||i==1||order==ceil(Int, dg[i-1]/2)
                for j = 1:length(supp[i])
                    add_clique!(G, unique(supp[i][j]))
                end
            else
                temp=copy(supp[i][1])
                for j=2:length(supp[i])
                    append!(temp, supp[i][j])
                end
                add_clique!(G, unique(temp))
            end
        end
        if alg=="NC"
            cliques,cql,cliquesize=max_cliques(G)
        else
            cliques,cql,cliquesize=chordal_cliques!(G, method=alg, minimize=minimize)
        end
    end
    uc=unique(cliquesize)
    numb=[sum(cliquesize.== i) for i in uc]
    println("------------------------------------------------------")
    println("The clique sizes of varibles:\n$uc\n$numb")
    println("------------------------------------------------------")
    return cliques,cql,cliquesize
end

function sadd(a, b; nb=0)
    c=[a;b]
    sort!(c)
    if nb>0
        i=1
        while i<length(c)
            if c[i]<=nb
                if c[i]==c[i+1]
                    deleteat!(c, i:i+1)
                else
                    i+=1
                end
            else
                break
            end
        end
    end
    return c
end

function approx_sol(opt, moment, n, cliques, cql, cliquesize, supp, coe; numeq=0, tol=1e-4)
    qsol=Float64[]
    lcq=sum(cliquesize)
    A=zeros(lcq,n)
    q=1
    for k=1:cql
        cqs=cliquesize[k]
        F=eigen(moment[k], cqs+1:cqs+1)
        temp=sqrt(F.values[1])*F.vectors[:,1]
        temp=temp[2:cqs+1]./temp[1]
        append!(qsol, temp)
        for j=1:cqs
            A[q,cliques[k][j]]=1
            q+=1
        end
    end
    sol=(A'*A)\(A'*qsol)
    flag=0
    upper_bound=seval(supp[1], coe[1], sol)
    gap=abs(upper_bound)>1 ? abs((opt-upper_bound)/upper_bound) : abs(opt-upper_bound)
    if gap >= tol
        flag=1
    end
    m=length(supp)-1
    for i=1:m-numeq
        if seval(supp[i+1], coe[i+1], sol)<=-tol
            flag=1
        end
    end
    for i=m-numeq+1:m
        if abs(seval(supp[i+1], coe[i+1], sol))>=tol
            flag=1
        end
    end
    if flag==0
        println("Global optimality certified!")
    end
    return sol,flag
end

function get_moment(measure, tsupp, cliques, cql, cliquesize; nb=0)
    moment=Vector{Union{Float64, Symmetric{Float64}, Array{Float64,2}}}(undef, cql)
    ltsupp=length(tsupp)
    for i=1:cql
        lb=cliquesize[i]+1
        moment[i]=zeros(Float64,lb,lb)
        for j=1:lb, k=j:lb
            if j==1
                if k==1
                    bi=UInt16[]
                else
                    bi=[cliques[i][k-1]]
                end
            else
                bi=sadd(cliques[i][j-1], cliques[i][k-1], nb=nb)
            end
            Locb=bfind(tsupp, ltsupp, bi)
            moment[i][j,k]=measure[Locb]
        end
        moment[i]=Symmetric(moment[i],:U)
    end
    return moment
end

function ncbfind(A, l, a)
    low=1
    high=l
    while low<=high
        mid=Int(ceil(1/2*(low+high)))
        if A[mid]==a
           return mid
        elseif A[mid]<a
            high=mid-1
        else
            low=mid+1
        end
    end
    return 0
end

function seval(supp, coe, x)
    val=0
    for i=1:length(supp)
        if isempty(supp[i])
            temp=1
        else
            temp=prod(x[supp[i][j]] for j=1:length(supp[i]))
        end
        val+=coe[i]*temp
    end
    return val
end
