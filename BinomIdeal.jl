#functions in this file:

#isCellular(I::Singular.sideal)
#saturate(I::Singular.sideal, J::Singular.sideal)
#cellularDecomp(I::Singular.sideal)
#isBinomial(f::Singular.spoly)
#isBinomialIdeal(I::Singular.sideal)
#isUnital(I::Singular.sideal)
#nemo(a::Singular.n_unknown{})
#lead_coeff(f::Singular.spoly)
#intersectionArray(A::Array{Singular.sideal,1})
#extractInclusionMinimalIdeals(A::Array{Any,1})
#removeSomeRedundancies(A::Array{Any,1})
#monomialFromVector(a::Array{Int64,1}, R::Singular.PolyRing)
#markov4ti2(L::fmpz_mat)
#"=="(I::Singular.sideal,J::Singular.sideal)
#isSubset(I::Singular.sideal,J::Singular.sideal)
#idealFromCharacter(P::PChar, R::Singular.PolyRing)
#partialCharacterFromIdeal(I::Singular.sideal, R::Singular.PolyRing)
#cellularStandardMonomials(I::Singular.sideal)
#witnessMonomials(I::Singular.sideal)
#cellularPrimaryDecomposition(I::Singular.sideal)
#cellularMinimalAssociatedPrimes(I::Singular.sideal)
#cellularAssociatedPrimes(I::Singular.sideal)
#cellularHull(I::Singular.sideal)


###################################################################################
#
#	Helper functions
#
###################################################################################

function saturate(I::Singular.sideal,J::Singular.sideal)
	#input: two ideals in the same ring
	#output: array with two entries: the first is the saturation of I with respect to J
	#the second is an integer k for which I:J^k=I:J^(k+1)=I:J^\infty

	check_parent(I,J)
	flag=true
	k=0
	If=I
	Iff=I	
	while flag
		Iff=quotient(If,J)
		if isSubset(Iff,If)==true
			flag =false
			return [If,k]
		else
			k=k+1
		end
		If=Iff
	end
end

function isBinomial(f::Singular.spoly)
	#check if the input polynomial is a binomial
	if Singular.length(f)<=2
		return(true)
	else 
		return(false)
	end
end

function isBinomialIdeal(I::Singular.sideal)
	#check if the input ideal is a binomial ideal
	#compute reduced GB and check if all elements in the GB are binomials
	
	I=std(I,complete_reduction=true)
	for i=1:Singular.ngens(I)
		if isBinomial(I[i])==false
			return(false)
		end
	end
	return(true)
end 

function isUnital(I::Singular.sideal)
	#check if I is a pure difference binomial ideal 
	#for this look at all elements in a reduced GB and check if they are pure difference
	#binomials

	I=std(I,complete_reduction=true)
	counter=0
	for i=1:Singular.ngens(I)
		if isBinomial(I[i])==false
			return false
		end
		if length(I[i])==2 && coeff(I[i],0)==1 && coeff(I[i],1)==-1
			counter=counter+1
		end
		if length(I[i])==2 && coeff(I[i],0)==-1 && coeff(I[i],1)==1
			counter=counter+1
		end
		if length(I[i])==1 #case I[i] is monomial
			counter=counter+1
		end
	end
	if counter==Singular.ngens(I)	
		return true
	else 
		return false
	end
end

function markov4ti2(L::fmpz_mat)
	#sanity checks noch einbauen!!
	nc=cols(L)
	nr=rows(L)
	#have to prepare an input file for 4ti2
	#create the file julia4ti2.lat
	f=open("julia4ti2.lat","w")
	write(f,"$nr ")
	write(f,"$nc \n")

	for i=1:nr
		for j=1:nc
			write(f,"$(L[i,j]) ")
		end
		write(f,"\n")
	end		
	close(f)
	
	#now we have the file julia4ti2.lat in the current working directory
	#can run 4ti2 with this input file to get a markov basis
	run(`/usr/bin/markov julia4ti2`)
	#this creates the file julia4ti2.mar with the markov basis
	
	#now we have to get the matrix from julia4ti2.mat in julia
	#this is an array of thype Any
	helpArray=readdlm("julia4ti2.mar")
	sizeHelpArray=size(helpArray)
	
	#the size of the markov basis matrix is
	nColMarkov=Int(helpArray[1,2])
	nRowMarkov=Int(helpArray[1,1])
	
	#now we have convert the lower part of the array helpArray into an Array of type Int64
	helpArrayInt=Array(Int64,nRowMarkov,nColMarkov)
	
	for i=2:(nRowMarkov+1)
		for j=1:nColMarkov
		helpArrayInt[i-1,j]=helpArray[i,j]
		end
	end
	
	#remove constructed files 
	run(`rm julia4ti2.lat`)
	run(`rm julia4ti2.mar`)	
	
	return helpArrayInt
end

function monomialFromVector(a::Array{Int64,1}, R::Singular.PolyRing)
	#returns the monomial corresponding to an exponent vector

	Variables=Singular.gens(R)
	monom=R(1)
	for i=1:Singular.ngens(R)
		monom=monom*Variables[i]^a[i]
	end
	return monom
end

function lead_coeff(f::Singular.spoly)
	return(coeff(f,length(f)-1))
end

function matrixFromArray(A::Array{Int64,1})
	#returns a matrix over FlintZZ with the entries of A transposed
	Mat=zeros(Int64,size(A,1),1)
	MatFlint=matrix(FlintZZ,size(A,1),1,Mat)
	for i=1:size(A,1) 
		MatFlint[i,1]=A[i]
	end
	return(MatFlint)
end

function nemo(a::Singular.n_unknown{})
	#returns the nemo value of a Singular.n_unknown element
	return Singular.libSingular.julia(a.ptr)
end

import Base.==

function ==(I::Singular.sideal,J::Singular.sideal)
	if isSubset(I,J)==true && isSubset(J,I)==true
		return true
	else 
		return false
	end
end

function isSubset(I::Singular.sideal,J::Singular.sideal)
	#returns true if I is contained in J
	#else returns false
	if J.isGB==false
		J=std(J)
	end
	testIdeal=reduce(I,J)
	if iszero(testIdeal)==true
		return true
	end
	return false	
end

function removeSomeRedundancies(A::Array{Any,1})
	#input:Array of ideals
	#output:Array of ideals consisting of some ideals less which give the same interseciton as
	#all ideals before
	
	Result=A
	for i=size(A,1):-1:1
		k=i-1
		flag=true
		while flag==true && k>0
			if isSubset(Result[k],Result[i])==true
				flag=false	#we can remove the ideal Result[i]
			end
			k=k-1
		end	
		if flag==false
			deleteat!(Result,i)
		end
	end

	for i=size(Result,1):-1:1
		k=i-1
		flag=true
		while flag==true && k>0
			if isSubset(Result[i],Result[k])==true
				flag=false 	#we can remove the ideal Result[k]
			else
				k=k-1
			end
		end
		if flag == false
			deleteat!(Result,k)
		end
	end

	return Result
end

function extractInclusionMinimalIdeals(A::Array{Any,1})
	#returns all ideals of A which are minimal with respect to inclusion
	
	n=size(A,1)
	#work with a copy of A
	Result=A
	
	while n>0
		if typeof(Result[1])!= Singular.sideal{Singular.spoly{Singular.n_unknown{QabElem}}}
			error("input has to be an Array of ideals") 
		end
		helpIdeal=Result[1]
		#now delete ideal from Array
		deleteat!(Result,1)
		flag=true 	#if ideal helpIdeal is redundant the flag is false
		k=1
		while flag==true && k<=size(Result,1)
			if isSubset(Result[k],helpIdeal)==true
				flag=false
			end
			k=k+1
		end
		if flag==true
			Result=[Result;helpIdeal]
		end
		n=n-1			
	end		
	return Result
end 

function extractInclusionMinimalIdeals(A::Array{Singular.sideal,1})
	#returns all ideals of A which are minimal with respect to inclusion

	n=size(A,1)
	#work with a copy of A
	Result=A
	
	while n>0
		helpIdeal=Result[1]
		#now delete ideal from Array
		deleteat!(Result,1)
		flag=true 	#if ideal helpIdeal is redundant the flag is false
		k=1
		while flag==true && k<=size(Result,1)
			if isSubset(Result[k],helpIdeal)==true
				flag=false
			end
			k=k+1
		end
		if flag==true
			Result=[Result;helpIdeal]
		end
		n=n-1			
	end		
	return Result
end 

function deleteZerosInHNF(m::fmpz_mat)
	#deletes zero rows in the hnf of m
	m=hnf(m)
	i=rows(m)
	cm=cols(m)
	s=sub(m,i:i,1:cm)
	ZeroTest=matrix(FlintZZ,1,cm,zeros(Int64,1,cm))
	while s==ZeroTest
		m=sub(m,1:(rows(m)-1),1:cm)
		i=rows(m)
		s=sub(m,i:i,1:cm)
	end
	return m
end


###################################################################################
#
#	Functions concerning a cellular decomposition
#
###################################################################################

function isCellular(I::Singular.sideal)
	#input: binomial ideal in a polynomial ring 
	#output: the decision true/false whether I is cellular or not
	#if it is cellular, return true and the cellular variables, otherwise return the 
	#index of a variable which is a zerodivisor but not nilpotent modulo I
	if I.isGB==false	
		I=std(I)
	end
	
	if (isBinomialIdeal(I)==false)
		error("Input ideal is not binomial")
	end

	if iszero(I)==true
		return(false,-1)
	end

	if I[1]==1
		return(false,-1)
	end
	
	DeltaC=Int64[]
	Delta=Int64[]
	Variables=Singular.gens(I.base_ring)
	helpideal=Ideal(I.base_ring)
	
	for i=1:Singular.ngens(I.base_ring)
		helpideal=Ideal(I.base_ring,Variables[i])
		satu=saturate(I,helpideal)
		if (std(satu[1])[1])!=1
			push!(Delta,i)
		end
	end
	
	#compute product of ring variables in Delta
	prodRingVar=one(I.base_ring)
	for k in Delta
		prodRingVar=prodRingVar*Variables[k]
	end
	
	prodRingVarIdeal=Ideal(I.base_ring,prodRingVar)
	J=saturate(I,prodRingVarIdeal)
	
	if isSubset(J[1],I)==true
		#then I==J
		#in this case I is cellular with respect to Delta
		return(true,Delta)
	else
		for i in Delta
		J=quotient(I,Ideal(I.base_ring,Variables[i]))
		if iszero(reduce(J,I))==false
		#if Singular.ngens(std(reduce(J,I)))!=0
			return (false,i)
		end
		end		
	end
end

function cellularDecomp(I::Singular.sideal) #with less redundancies
	#input: binomial ideal I
	#output: a cellular decomposition of I

	if (isBinomialIdeal(I)==false)
		error("Input ideal is not binomial")
	end

	A=isCellular(I)
	if A[1]==true
		return [I]
	end
	
	#choose a variable which is a zero divisor but not nilptent modulo I -> A[2] (if not dummer fall)
	#determine the power s s.t. (I:x_i^s)==(I:x_i^infty)
	satu=saturate(I,Ideal(I.base_ring,Singular.gens(I.base_ring)[A[2]]))
	s=satu[2]
	#now compute the cellular decomposition of the binomial ideals (I:x_i^s) and I+(x_i^s)
	#by recursively calling the algorithm
	Decomp=Singular.sideal[]
	I1=satu[1]
	I2=I+Ideal(I.base_ring,(Singular.gens(I.base_ring)[A[2]])^s)
	
	DecompI1=cellularDecomp(I1)
	DecompI2=cellularDecomp(I2)
	
	#now check for redundancies
	redTest=Ideal(I.base_ring,one(I.base_ring))
	redTestIntersect=Ideal(I.base_ring,one(I.base_ring))
	
	for i=1:size(DecompI1,1)
		redTestIntersect=Singular.intersection(redTest,DecompI1[i])
		if Singular.ngens(std(reduce(redTest,std(redTestIntersect))))!=0
			#ideal not redundant
			Decomp=[Decomp;DecompI1[i]]
		end
		redTest=redTestIntersect
	end
	for i=1:size(DecompI2,1)
		redTestIntersect=Singular.intersection(redTest,DecompI2[i])
		if iszero(reduce(redTest,std(redTestIntersect)))==false
			#ideal not redundant
			Decomp=[Decomp;DecompI2[i]]
		end
		redTest=redTestIntersect
	end	
	return Decomp
end 

function cellularDecompMacaulay(I::Singular.sideal) 
	#algorithm after Macaulay2 implementation for computing a cellular decomposition of a binomial ideal
	#seems to be faster than cellularDecomp, but there are still examples which are really slow
	
	if (isBinomialIdeal(I)==false)
		error("Input ideal is not binomial")
	end

	R=base_ring(I)
	n=Singular.ngens(R)	
	intersectAnswer=Ideal(R,R(1))
	Answer=Singular.sideal[]
	ToDo=[([R(1)],Singular.gens(R),I)]
	#every element in the todo list has three dedicated data:
	#1: contains a list of variables w.r.t. which it is already saturated 
	#2: conatains variables to be considered for cell variables
	#3: is the ideal to decompose

	compo=0
	while size(ToDo,1)>0
		L=ToDo[1]

		if size(ToDo,1)>1
			ToDo=ToDo[2:size(ToDo,1)]
		else 
			ToDo=[]
		end		

		if iszero(reduce(intersectAnswer,std(L[3])))==true
			#found redundant component
		elseif size(L[2],1)==0 
			#no variables remain to check -> we have an answer
			compo=compo+1
			newone=L[3] #ideal 
			Answer=[Answer;newone]
			intersectAnswer=Singular.intersection(intersectAnswer,newone)
			if intersectAnswer==I
				ToDo=[]
			end
		else
			#there are remaining variables 
			i=L[2][1] 	#variable under consideration
			if size(L[2],1)>1
				newL2=L[2][2:size(L[2],1)]	
			else
				newL2=[]			
			end
			result=saturate(L[3],Ideal(R,i))
			J=result[1]  	#ideal
			k=result[2]	#saturation exponent
			if k>0
				#if a division was needed we add the monomial i^k to the ideal
				#under consideration
				J2=L[3]+ Ideal(R,i^k)
				
				#compute product of all variables in L[1]
				prod=R(1)
				for m=1:size(L[1],1)
					prod=prod*L[1][m]
				end
				J2=saturate(J2,Ideal(R,prod))[1]
				if isSubset(Ideal(R,R(1)),J2)==false
					#we have to decompose J2 further
					ToDo=[ToDo; (L[1],newL2,J2)]
				end
			end
			#continue with the next variable and add i to L[1]
			if isSubset(Ideal(R,R(1)),J)==false
				ToDo=[ToDo;([L[1];i], newL2, J)]
			end
			
		end
	end 
	return extractInclusionMinimalIdeals(Answer)
end


###################################################################################
#
#	Partial characters and ideals
#
###################################################################################

function idealFromCharacter(P::PChar, R::Singular.PolyRing)
	#input: partial character P and a polynomial ring R
	#output: the ideal $I_+(P)=\langle x^{u_+}- P(u)x^{u_-} \mid u \in P.A \rangle$

	@assert cols(P.A)==Singular.ngens(R)
	#test if the domain of the partial character is the zero lattice
	Zero=matrix(FlintZZ,1,cols(P.A),zeros(Int64,1,cols(P.A)))
	if rows(P.A)==1 && LatticeEqual(P.A,Zero)==true
		return Ideal(R,zero(R))
	end

	#now case if P.A is the identity matrix 
	#then the ideal generated by the generators of P.A suffices and gives the whole ideal I_+(P)
	#note that we can only compare the matrices if P.A is a square matrix
	if cols(P.A)==rows(P.A)
		id=convert(Array{Int64},eye(cols(P.A)))
		ID=matrix(FlintZZ,cols(P.A),cols(P.A),id)
		if P.A==ID
			return(makeBinomials(P,R))	
		end
	end

	#now check if the only values of P taken on the generators of the lattice is one
	#then we can use markov bases
	#simple test
	test=true
	i=1
	Variables=Singular.gens(R)
	I=Ideal(R,zero(R))

	while test==true && i<=size(P.b,1)
		if P.b[i]!=QabField()(1)
			#in this case there is a generator g for which P(g)!=1
			test=false
		end
		i=i+1
	end
	
	if test==true
		#then we can use markov bases to get the ideal
		A=markov4ti2(P.A)
		#now get the ideal corresponding to the computed markov basis
		nr=size(A,1)	#number of rows
		nc=size(A,2)	#number of columns
		#-> we have nr generators for the ideal
		#for each row vector compute the corresponding binomial
		for k=1:nr
			monomial1=one(R)
			monomial2=one(R)
			for s=1:nc
				if A[k,s]<0
					monomial2=monomial2*Variables[s]^(-A[k,s])
				else 
					monomial1=monomial1*Variables[s]^(A[k,s]) 
				end
			end
			#the new generator for the ideal is monomial1-minomial2
			I=I+Ideal(R,monomial1-monomial2)
		end	
		return I
	end

	#now consider the last case where we have to saturate      
	I=makeBinomials(P,R)
	#now we have to saturate the ideal by the product of the ring variables
	varProduct=one(R)
	for i=1:Singular.ngens(R)
		varProduct=varProduct*Variables[i]
	end	

	return saturate(I,Ideal(R,varProduct))[1]
end 

function makeBinomials(P::PChar, R::Singular.PolyRing)
	#output: ideal generated by the binomials corresponding to the generators of the domain P.A of the partial character P
	#Note: This is not the ideal I_+(P)!!

	@assert cols(P.A)==Singular.ngens(R)
	nc=cols(P.A)	#number of columns
	nr=rows(P.A)	#number of rows
	Variables=Singular.gens(R)
	#-> we have nr binomial generators for the ideal
	I=Ideal(R,zero(R))

	for k=1:nr
			monomial1=one(R)
			monomial2=one(R)
			for s=1:nc
				if P.A[k,s]<0
					monomial2=monomial2*Variables[s]^(Int64(-P.A[k,s]))
				else 
					monomial1=monomial1*Variables[s]^(Int64(P.A[k,s])) 
				end
			end
			#the new generator for the ideal is monomial1-P.b[k]*monomial2
			I=I+Ideal(R,monomial1-P.b[k]*monomial2)
	end	
	return I
end

function partialCharacterFromIdeal(I::Singular.sideal, R::Singular.PolyRing)
	#input: cellular binomial ideal
	#output: the partial character corresponding to the ideal I \cap k[\mathbb{N}^\Delta] 
	
	#first test if the input ideal is really a cellular ideal
	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")	
	end

	Delta=cell[2]	#cell variables
	if size(Delta,1)==0
		P=PChar(matrix(FlintZZ,1,Singular.ngens(R), zeros(Int64,1,Singular.ngens(R))), [QabField()(1)], Set{Int64}(Delta))
		return P	
	end	
	
	#now consider the case where Delta is not empty
	#fist compute the intersection I \cap k[\Delta]
	#for this use eliminate function from Singular. We first have to compute the product of all 
	#variables not in Delta
	prodDeltaC=R(1)
	Variables=Singular.gens(R)
	for i=1:Singular.ngens(R)
		if (i in Delta)==false
			prodDeltaC=prodDeltaC*Variables[i]
		end
	end
	J=Singular.eliminate(I, prodDeltaC)
	if iszero(J)==true	
	#if Singular.ngens(J)==0 || (Singular.ngens(J)==1 && J[1]== R(0))	
		#return another trivial character
		#lattice has only one generator, namely the zero vector
		P=PChar(matrix(FlintZZ,1,Singular.ngens(R), zeros(Int64,1,Singular.ngens(R))), [QabField()(1)], Set{Int64}(Delta))
		return P
	end
	#now case if J \neq 0
	#let ts be a list of minimal binomial generators for J
	J=std(J,complete_reduction=true)
	ts=Array{Singular.spoly}[]
	for i=1:Singular.ngens(J)
		ts=[ts; J[i]]
	end	
	vs=zeros(Int64,Singular.ngens(R),1)
	images=QabElem[]
	for t in ts
		tCopy=t
		u=lead_exponent(t)
		m=monomialFromVector(u,R)
		tCopy=tCopy-m
		v=lead_exponent(tCopy)
		#now test if we need the vector uv
		uv=matrixFromArray(u-v)	#this is the vector of u-v
		vst=transpose(vs)
		vstMat=matrix(FlintZZ,size(vst,1), size(vst,2),vst)
		if(cansolve(transpose(vstMat),uv)[1]==false)	
			images=[images; nemo(-lead_coeff(tCopy))]
			#we have to save u-v as generator for the lattice
			#now concatenate the vector vs on bottom of the matrix vs
			vs=[vs (u-v)]
		end
	end
	#now vs has a zero in the left column and we have to delete it
	#but first we have to transpose vs
	vs=transpose(vs)
	
	vs=vs[2:size(vs,1),1:size(vs,2)]	
	#now convert to matrix	
	vsMat=matrix(FlintZZ,size(vs,1), size(vs,2),vs)
	#delete zero rows in the hnf of vsMat so that we do not get problems when considering a 
	#saturation
	vsMat=deleteZerosInHNF(vsMat)
	P=PChar(vsMat, images , Set{Int64}(Delta))
	return P
end 


###################################################################################
#
#	Embedded associated lattice witnesses and hull
#
###################################################################################

function cellularStandardMonomials(I::Singular.sideal)
	#input: cellular ideal I
	#output: the standardmonomials of the ideal I \cap k[\mathbb{N}^{\Delta^c}], 
	#this are only finitely many!

	if I.isGB==false
		I=std(I)
	end
	
	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")
	end

	R=Singular.base_ring(I)

	#now we start computing the standardmonomials
	#first determine the set Delta^c of noncellular variables
	DeltaC=Array{Int64}[]
	for i=1: Singular.ngens(R)
		if (i in cell[2])==false
			DeltaC=[DeltaC;i]
		end
	end
	
	#eliminate the variables in Delta
	prodDelta=R(1)
	Variables=Singular.gens(R)
	for i in cell[2]
		prodDelta=prodDelta*Variables[i]
	end
	
	J=Singular.eliminate(I, prodDelta)
	
	leadIdeal=lead(J)
	leadIdeal=std(leadIdeal)

	mon=Array{Singular.spoly}[]	#this will hold set of standard monomials	
	Answer=Array[]	
	Result=Array{Singular.spoly}[]

	for i in DeltaC
		flag=true
		mon=[mon;Variables[i]^0]
		d=1
		while flag ==true
			if reduce(Variables[i]^d,I) == 0
				flag=false
			else
				mon=[mon;Variables[i]^d]
				d=d+1
			end
			
		end
		push!(Answer,mon)
		mon=Array{Singular.spoly}[]
	end 

	for a in product(Answer)
		testmon=R(1)
		for l in a 
			testmon=testmon*l
		end		
		if reduce(testmon,leadIdeal)!= 0 
			Result=[Result;testmon]
		end
	end
	return Result
end

function witnessMonomials(I::Singular.sideal)
	#input: cellular binomial ideal
	#output: M_{emb}(I) (not the ideal, but the generators of it in an array)

	#test if input ideal is cellular
	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")
	end

	R=Singular.base_ring(I)
	Delta=cell[2]
	
	#compute the PChar corresponding to I and the standard monomials of I \cap k[N^Delta]
	P=partialCharacterFromIdeal(I, R)
	M=cellularStandardMonomials(I)	#array of standard monomials, this is our to-do list
	Memb=Singular.spoly[]	#this will hold our set of witness monomials
	Iquotm=Ideal(R,R(0))
	Pquotm=partialCharacterFromIdeal(I, R)

	while size(M,1)!=0
		Iquotm=Singular.quotient(I,Ideal(R,M[1]))
		Pquotm=partialCharacterFromIdeal(Iquotm, R)
		if rank(Pquotm.A)>rank(P.A)
			Memb=[Memb;M[1]]
		end
		#by checking for divisibility of the monomials in M by M[1] respectively of M[1]
		#by monomials in M, some monomials in M necessarily belong to Memb, respectively can 			#be directly excluded from being elements of Memb
		#todo: implement this for improvement
		deleteat!(M,1)
	end	
	return(Memb)
end		

function cellularHull(I::Singular.sideal)
	#input: cellular binomial ideal 
	#ouput: hull(I), the intersection of all minimal primary components of I
	#by theorems we know that Hull(I)=M_emb(I)+I
	
	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")
	end
	
	#now construct the ideal M_emb with the above algorithm witnessMonomials
	Memb=Ideal(I.base_ring,R(0))	#this will hold the ideal M_emb(I)
	M=witnessMonomials(I)
	
	for m in M
		Memb=Memb + Ideal(R,m)
	end
	
	return (I+Memb)	
end


###################################################################################
#
#	Associated primes
#
###################################################################################	

function cellularAssociatedPrimes(I::Singular.sideal)
	#input: cellular binomial ideal
	#output: the set of associated primes of I
	
	if isUnital(I)==false
		error("input ideal has to be a pure difference binomial ideal")
	end

	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")
	end

	if I.isGB==false
		I=std(I)
	end
	
	Ass=Array{Singular.sideal}[]	#this will hold the set of associated primes of I
	Variables=Singular.gens(I.base_ring)
	U=cellularStandardMonomials(I)	#set of standard monomials

	#construct the ideal (x_i \mid i \in \Delta^c)
	idealDeltaC=Ideal(R,R(0))
	for i=1:Singular.ngens(I.base_ring)
		if (i in cell[2])==false
			idealDeltaC=idealDeltaC + Ideal(I.base_ring,Variables[i])
		end
	end		
	
	for m in U
		Im=Singular.quotient(I,Ideal(I.base_ring,m))
		Pm=partialCharacterFromIdeal(Im,Im.base_ring)
		#now compute all saturations of the partial character Pm
		PmSat=PCharSaturateAll(Pm)					
		for P in PmSat
			Ass=[Ass; (idealFromCharacter(P, I.base_ring)+idealDeltaC)]
		end
	end

	#now check if there are superflous elements in Ass
	for i=size(Ass,1):-1:1
		j=i-1
		flag = false
		while (j>0 && flag==false)
			if Ass[j]==Ass[i]
			 	deleteat!(Ass,i)
				flag =true
			end
			j=j-1
		end
	end	
	
	return Ass
end

function cellularMinimalAssociatedPrimes(I::Singular.sideal)
	#input: cellular pure difference binomial ideal
	#output: the set of minimal associated primes of I
		
	if isUnital(I)==false
		error("input ideal is not a pure difference binomial ideal")
	end

	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")
	end

	P=partialCharacterFromIdeal(I,I.base_ring)
	PSat=PCharSaturateAll(P)	
	minAss=Array{Singular.sideal}[]	#this will hold the set of minimal associated primes
	
	#construct the ideal (x_i \mid i \in \Delta^c)
	Variables=Singular.gens(I.base_ring)
	idealDeltaC=Ideal(R,R(0))
	for i=1:Singular.ngens(I.base_ring)
		if (i in cell[2])==false
			idealDeltaC=idealDeltaC + Ideal(I.base_ring,Variables[i])
		end
	end	

	for Q in PSat
		minAss=[minAss; (idealFromCharacter(Q,I.base_ring)+idealDeltaC)]
	end
		
	return minAss
end

function binomialAssociatedPrimes(I::Singular.sideal)
	#input: pure difference binomial ideal 
	#output: the associated primes, but only implemented effectively in the cellular case	
	#in the noncellular case compute a primary decomp and take radicals
	
	if isUnital(I)==false
		error("input ideal is not a pure difference binomial ideal")
	end

	cell=isCellular(I)
	if cell[1]==true
		return cellularAssociatedPrimes(I)
	end
		
	#now consider the case when I is not cellular and compute a primary decomposition
	PD=binomialPrimaryDecomposition(I)
	
	#todo: take radicals and delete the superfluous elements from the array
	error("not yet implemented")	
	return 1
end


###################################################################################
#
#	Primary decomposition
#
###################################################################################

function cellularPrimaryDecomposition(I::Singular.sideal)    #algorithm from macaulay2
	#input: pure difference cellular binomial ideal in k[x]
	#output: binomial primary ideals which form a minimal primary decomposition of I

	if isUnital(I)==false
		error("input ideal is not a pure difference binomial ideal")
	end	
	
	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")
	end

	#compute associated primes
	Ass=cellularAssociatedPrimes(I)
	C=Singular.sideal[]	#this will hold the set of primary components
	
	#compute product of all non cellular variables and the product of all cell variables
	prodDeltaC=R(1)	
	prodDelta=R(1)
	Variables=Singular.gens(I.base_ring)
	for i=1:Singular.ngens(R)
		if (i in cell[2])==false
			prodDeltaC=prodDeltaC*Variables[i]
		else 
			prodDelta=prodDelta*Variables[i]
		end
	end
	
	for P in Ass
		helpIdeal=I+eliminate(P,prodDeltaC)
		#now saturate the ideal with respect to the cellular variables
		helpIdeal=saturate(helpIdeal,Ideal(I.base_ring,prodDelta))
		C=[C; cellularHull(helpIdeal[1])]
	end
	return C
end

function binomialPrimaryDecomposition(I::Singular.sideal)
	#input: pure difference binomial ideal 
	#output: binomial primary ideals which form a not necessarily 
	#minimal primary decomposition of I

	#first compute a cellular decomposition of I
	#cellComps=cellularDecomp(I)
	cellComps=cellularDecompMacaulay(I)
	
	C=Array{Singular.sideal}[]	#this will hold the set of primary components
	
	#now compute a primary decomposition of each cellular component 
	for J in cellComps
		C=[C; cellularPrimaryDecomposition(J)]
	end
	
	#remove some redundancies 
	C=removeSomeRedundancies(C)
	return C		
end

