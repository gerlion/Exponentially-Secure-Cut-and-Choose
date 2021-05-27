all : vectorspace.vo

#all .vo file dependes on .v file
%.vo : %.v
	coqc -R ../ "" $*.v

#compile groups.v
groups.vo : groups.v

module.vo : groups.vo module.v

vectorspace.vo : module.vo vectorspace.v


#run clean
clean :
	rm -rf *.vo *.vos *.vok .*.cache *.glob .*.aux

