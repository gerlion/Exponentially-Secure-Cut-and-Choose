#all .vo file dependes on .v file
%.vo : %.v
	coqc -R Groups Groups $*.v

# compile coqprime file
VectorUtil.vo : VectorUtil.v

makeGroups : VectorUtil.vo 
	make -C Groups

#compile singmaprotocol.v
sigmaprotocol.vo : makeGroups sigmaprotocol.v 

newProofOfShuffle.vo : sigmaprotocol.vo newProofOfShuffle.v 


#run clean
clean :
	rm -rf *.vo *.vos *.vok *.glob .*.aux .lia.* && cd Groups && make clean && cd ..