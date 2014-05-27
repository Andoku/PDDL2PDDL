package PDDL2PDDL;


import java.util.*;


import pddl4j.PDDLObject;

import PDDL2PDDL.Analyzer;
import PDDL2PDDL.Generator;
import PDDL2PDDL.Transformation;
import PDDL2PDDL.EqualityTransformation;
import PDDL2PDDL.DisjunctivePreconditionsTransformation;
import PDDL2PDDL.UniversalPreconditionsTransformation;

class Pddl2pddl {
	public static void main(String[] args) throws Exception {
	
    	if (args.length != 3) {
        	System.err.println("Invalid command line");
    	} else {
			ArrayList<PDDLObject> desc = Analyzer.parse(args[1], args[2]);
			PDDLObject domain = desc.get(0);
			PDDLObject problem = desc.get(1);
		
			if (args[0].equals(":equality")) {
				EqualityTransformation.transform(domain, problem);
			} else if (args[0].equals(":disjunctive-preconditions")) {
				DisjunctivePreconditionsTransformation.transform(domain, problem);
			} else if (args[0].equals(":universal-preconditions")){
				UniversalPreconditionsTransformation.transform(domain, problem);
			} else {
				System.err.println("Invalid command line");
			}
		
			Generator.print(domain);
			Generator.print(problem);
    	}
	}
}