package wv_oef;

public class Term {
	
	public Term(int kardinaliteit, String newName) {
		this.setKardinaliteit(kardinaliteit);
		this.setInterneTerm(new Term[this.getKardinaliteit()]);
		this.setName(newName);
	}
	
	private int kard;
	
	public int getKardinaliteit() {
		return kard;
	}
	
	public void setKardinaliteit(int kardinaliteit) {
		this.kard=kardinaliteit;
	}
	
	private Term[] interneTerm;
	
	public Term[] getInterneTerm() {
		return interneTerm;
	}
	
	public void setInterneTerm(Term[] term) {
		this.interneTerm = term;
	}
	
	private String name;
	
	public String getName() {
		return name;
	}
	
	public void setName(String newName) {
		this.name = newName;
	}
	
	public Term clone() {
		Term cloneTerm= new Term(this.getKardinaliteit(),this.getName());
		for (int i=0; i<this.getKardinaliteit();i++) {
			if(this.getInterneTerm()[i]!=null) {
				cloneTerm.getInterneTerm()[i]=this.getInterneTerm()[i].clone();
			}
		}
		return cloneTerm;
	}
	
	public boolean groundedTerm() {
		boolean grounded=true;
		for(int i=0; i<this.getKardinaliteit() && grounded;i++) {
			if(this.getInterneTerm()[i]==null) {
				grounded= false;
			}
			else {
				grounded = grounded && this.getInterneTerm()[i].groundedTerm();
			}
		}
		return grounded;

	}

    @Override
    public String toString() { 
    	if(this.getKardinaliteit()==0) {
    		return this.getName();
    	}
    	else
    	{
    		String result= this.getName() + "(";
    		for (int i=0; i< this.getKardinaliteit()-1; i++) {// 1 minder comma dan de kardinaliteit
    			result= result + this.getInterneTerm()[i].toString() + ",";
    		}
    		result= result + this.getInterneTerm()[this.getKardinaliteit()-1].toString() + ")";
    		return result;
    	
    		
    	}
    } 
}
