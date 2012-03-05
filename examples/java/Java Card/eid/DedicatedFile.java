package be.fedict.neweidapplet;

/*@
predicate file_element(File child;) = child == null ? true : [1/2]child.File(_, _, _);
predicate valid_id(File child;) = [_]child.fileID |->_;
@*/

public class DedicatedFile extends File {

	/*@ predicate File(short theFileID, boolean activeState, triple<DedicatedFile, list<File>, any> info) = 
		DedicatedFile(theFileID, ?dedFile, activeState, ?siblist, ?oinfo) &*& info == triple(dedFile, siblist, oinfo); @*/
	/*@ predicate DedicatedFile(short fileID, DedicatedFile parentFile, boolean activeState, list<File> siblist, any info) = 
		this.File(File.class)(fileID, activeState, _) &*& this.parentFile |-> parentFile &*& this.siblings |-> ?siblings &*& 
		siblings != null &*& siblings.length == MAX_SIBLINGS &*& array_slice(siblings, 0, siblings.length, ?sb) &*& this.number |-> ?number &*& siblist == take(number, sb) &*&
		number >= 0 &*& number <= DedicatedFile.MAX_SIBLINGS &*& info == unit &*&
		foreachp(take(number, sb), valid_id); @*/

	// link to parent DF
	public DedicatedFile parentFile;
	// list of sibling files (either EF or DF)
	private static final byte MAX_SIBLINGS = 10;
	private File[] siblings;
	// number of siblings
	private byte number;
	// constructor only used by MasterFile
	protected DedicatedFile(short fid) 
  	    //@ requires true;
      	    //@ ensures DedicatedFile(fid, null, true, nil, _);
	{
		super(fid);
		parentFile = null;
		siblings = new File[MAX_SIBLINGS];
		number = 0;
		//@ assert this.siblings |-> ?siblings;
		//@ assert array_slice(siblings, 0, siblings.length, ?siblist);
		//@ close foreachp(nil, valid_id);
		//@ close DedicatedFile(fid, null, true, nil, _);
	}
	public DedicatedFile(short fid, DedicatedFile parent) 
  	    //@ requires parent != null &*& parent.DedicatedFile(?fileID, ?pf, ?activeState, ?siblist, ?info);
      	    //@ ensures DedicatedFile(fid, parent, true, nil, _) &*& parent.DedicatedFile(fileID, pf, activeState, (length(siblist) < DedicatedFile.MAX_SIBLINGS ? append(siblist, cons(this, nil)) : siblist), info);
	{
		super(fid);
		parentFile = parent;
		siblings = new File[MAX_SIBLINGS];
		number = 0;
		parent.addSibling(this);
		//@ close foreachp(nil, valid_id);
		//@ close DedicatedFile(fid, parent, true, nil, _);
	}
	public DedicatedFile getParent() 
	    //@ requires DedicatedFile(?fid, ?parentfile, ?active, ?siblist, ?info);
	    //@ ensures DedicatedFile(fid, parentfile, active, siblist, info) &*& result == parentfile;
	{
		//@ open DedicatedFile(fid, parentfile, active, siblist, info);
		return parentFile;
		//@ close DedicatedFile(fid, parentfile, active, siblist, info);
	}
	
	protected void addSibling(File s) 
  	    //@ requires DedicatedFile(?fileID, ?parentFile, ?activeState, ?siblist, ?info) &*& valid_id(s);
  	    /*@ ensures DedicatedFile(fileID, parentFile, activeState, ?newSibList, info)
  	    		&*& newSibList == (length(siblist) < MAX_SIBLINGS ? append(siblist, cons(s, nil)) : siblist)
  	    		&*& length(siblist) < MAX_SIBLINGS ? mem(s, newSibList) == true : true; @*/
	{
		//@ open DedicatedFile(fileID, parentFile, activeState, siblist, info);
		//@ assert array_slice(?thesiblings, _, _, ?sb);
		//@ int snumber = length(siblist);
		if (number < MAX_SIBLINGS) {
			siblings[number++] = s;
			//@ take_one_more(snumber, update(snumber, s, sb));
			//@ assert array_slice(thesiblings, _, _, ?sb2);
			//@ assert sb2 == update(snumber, s, sb);
			//@ assert nth(snumber, update(snumber, s, sb)) == s;
			//@ assert take(snumber, sb) == take(snumber, update(snumber, s, sb));
			//@ assert take(snumber + 1, update(snumber, s, sb)) == append(take(snumber, update(snumber, s, sb)), cons(nth(snumber, update(snumber, s, sb)), nil));
			//@ close foreachp(nil, valid_id);
			//@ close foreachp(cons(s, nil), valid_id);
			//@ foreachp_append(take(snumber, sb), cons(s, nil));	
		}
		
		/*@ close DedicatedFile(fileID, parentFile, activeState,		 
			snumber < MAX_SIBLINGS ? append(take(snumber, siblist), cons(s, nil)) : siblist, 
			info); @*/
	}

	public File getSibling(short fid) 
  	    //@ requires [?f]DedicatedFile(?fileID, ?parentFile, ?activeState, ?siblist, ?info);
      	    //@ ensures [f]DedicatedFile(fileID, parentFile, activeState, siblist, info) &*& result == null ? true : mem(result, siblist) == true;
	{
		//@ open DedicatedFile(fileID, parentFile, activeState, siblist, info);
		//@ assert [f]array_slice(?thesiblings, _, _, ?sb);
		//@ int snumber = length(siblist);
		for (byte i = 0; i < number; i++) 
		/*@ invariant i >= 0 &*& [f]this.File(File.class)(fileID, activeState, _) &*& [f]this.parentFile |-> parentFile &*& [f]number |-> (byte) length(siblist) &*& [f]this.siblings |-> thesiblings &*& [f]array_slice(thesiblings, 0, thesiblings.length, sb)
		      &*& [f]foreachp(siblist, valid_id); @*/
		{
			//@ assert 0 <= i &*& i < thesiblings.length;
			File fl = siblings[i];
			//@ assert nth(i, siblist) == fl;
			//@ int tmp = thesiblings.length;
			//@ assert snumber <= tmp;
			//@ nth_take(i, snumber, sb);
			//@ assert nth(i, take(snumber, sb)) == nth(i, sb);
			//@ assert nth(i, take(snumber, sb)) == nth(i, sb);
			//@ assert nth(i, siblist) == fl;
			//@ mem_nth(i, siblist);
			//@ foreachp_remove<File>(fl, siblist);
			if (fl != null && fl.getFileID() == fid) {
				//@ foreachp_unremove<File>(fl, siblist);
				return fl;
				//@ close [f]DedicatedFile(fileID, parentFile, activeState, siblist, info);
			}
			//@ foreachp_unremove<File>(fl, siblist);
		}
		//@ close [f]DedicatedFile(fileID, parentFile, activeState, siblist, info);
		return null;
	}

        /*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public short getFileID() 
	    //@ requires [?f]valid_id(this);
	    //@ ensures [f]valid_id(this);
	{
		//@ open [f]valid_id(this);
		File thiz = this;
		return fileID;
		//@ close [f]valid_id(this);
	}
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public void setActive(boolean b)
	    //@ requires File(?fid, _, ?info);
	    //@ ensures File(fid, b, info);
	{
		//@ open File(fid, _, info);
		//@ open DedicatedFile(fid, ?d1, _, ?siblist, ?info2);
		File thiz = this;
		//@ open thiz.File(fid, _, ?info3);
		active = b;
		//@ close thiz.File(fid, b, info3);
		//@ close DedicatedFile(fid, d1, b, siblist, info2);
		//@ close File(fid, b, info);
	}
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public boolean isActive() 
	    //@ requires [?f]File(?fid, ?state, ?info);
	    //@ ensures [f]File(fid, state, info) &*& result == state;
	{
		//@ open [f]File(fid, state, info);
		//@ open [f]DedicatedFile(fid, ?d1, state, ?siblist, ?info2);
		//@ open this.File(File.class)(fid, state, ?info3);
		return active;
		//@ close [f]this.File(File.class)(fid, state, info3);
		//@ close [f]DedicatedFile(fid, d1, state, siblist, info2);
		//@ close [f]File(fid, state, info);
	}
	
	/*@ 
	lemma void castFileToDedicated()
            requires [?f]File(?fid, ?state, ?info);
            ensures switch (info) { case triple(dedFile, siblist, oinfo): return [f]DedicatedFile(fid, dedFile, state, siblist, oinfo); } ;
	{
	    open [f]File(fid, state, _);
    	}

	lemma void castDedicatedToFile()
            requires [?f]DedicatedFile(?fid, ?dedFile, ?state, ?siblist, ?oinfo);
            ensures [f]File(fid, state, triple(dedFile, siblist, oinfo));
	{
	    close [f]File(fid, state, triple(dedFile, siblist, oinfo));
    	}
    	@*/
}
