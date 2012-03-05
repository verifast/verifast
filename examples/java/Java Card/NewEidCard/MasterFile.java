package be.fedict.neweidapplet;

public /*VF*ADDED*/final class MasterFile extends DedicatedFile {
	//@ predicate File(short theFileID, boolean activeState, triple<DedicatedFile, list<File>, any> info) = MasterFile(theFileID, ?dedFile, activeState, ?siblist, ?oinfo) &*& info == triple(dedFile, siblist, oinfo);
	//@ predicate DedicatedFile(short fileID, DedicatedFile parentFile, boolean activeState, list<File> siblist, any info) = MasterFile(fileID, parentFile, activeState, siblist, info);
	//@ predicate MasterFile(short fileID, DedicatedFile parentFile, boolean activeState, list<File> siblist, any info) = this.DedicatedFile(DedicatedFile.class)(fileID, parentFile, activeState, siblist, _) &*& fileID == 0x3F00 &*& parentFile == null &*& info == unit;

	private static final short MF_FID = 0x3F00;
	public MasterFile() 
  	    //@ requires true;
      	    //@ ensures this.MasterFile(0x3F00, null, true, nil, _);
	{
		super(MF_FID);
		//@ close MasterFile(0x3F00, null, true, _, _);
	}
	
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public DedicatedFile getParent() 
	    //@ requires DedicatedFile(?fid, ?parentfile, ?active, ?siblist, ?info);
	    //@ ensures DedicatedFile(fid, parentfile, active, siblist, info) &*& result == parentfile;
	{
		//@ open DedicatedFile(fid, parentfile, active, siblist, info);
		//@ open MasterFile(fid, parentfile, active, siblist, ?info2);
		//@ open this.DedicatedFile(DedicatedFile.class)(fid, parentfile, active, siblist, ?info3);
		return parentFile;
		//@ close this.DedicatedFile(DedicatedFile.class)(fid, parentfile, active, siblist, info3);
		//@ close MasterFile(fid, parentfile, active, siblist, info2);
		//@ close DedicatedFile(fid, parentfile, active, siblist, info);
	}

	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public File getSibling(short fid) 
  	    //@ requires [?f]DedicatedFile(?fileID, ?parentFile, ?activeState, ?siblist, ?info);
      	    //@ ensures [f]DedicatedFile(fileID, parentFile, activeState, siblist, info) &*& result == null ? true : mem(result, siblist) == true;
	{
		//@ open [f]DedicatedFile(fileID, parentFile, activeState, siblist, info);
		//@ open [f]MasterFile(fileID, parentFile, activeState, siblist, info);
		return super.getSibling(fid);
		//@ close [f]MasterFile(fileID, parentFile, activeState, siblist, info);
		//@ close [f]DedicatedFile(fileID, parentFile, activeState, siblist, info);
	}
	
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public short getFileID() 
	    //@ requires [?f]valid_id(this);
	    //@ ensures [f]valid_id(this);
	{
		//@ open [f]valid_id(this);
		return fileID;
		//@ close [f]valid_id(this);
	}
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public void setActive(boolean b)
	    //@ requires File(?fid, _, ?info);
	    //@ ensures File(fid, b, info);
	{
		//@ open File(fid, _, info);
		//@ open MasterFile(fid, ?d0, _, ?d1, ?info2);
		//@ open this.DedicatedFile(DedicatedFile.class)(fid, null, _, d1, ?info3);
		//@ open this.File(File.class)(fid, _, ?info4);
		active = b;
		//@ close this.File(File.class)(fid, b, info4);
		//@ close this.DedicatedFile(DedicatedFile.class)(fid, null, b, d1, info3);
		//@ close MasterFile(fid, null, b, d1, info2);
		//@ close File(fid, b, info);
	}
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public boolean isActive() 
	    //@ requires [?f]File(?fid, ?state, ?info);
	    //@ ensures [f]File(fid, state, info) &*& result == state;
	{
		//@ open [f]File(fid, state, info);
		//@ open [f]MasterFile(fid, ?d0, state, ?d1, ?info2);
		//@ open [f]this.DedicatedFile(DedicatedFile.class)(fid, null, state, d1, ?info3);
		//@ open [f]this.File(File.class)(fid, state, ?info4);
		return active;
		//@ close [f]this.File(File.class)(fid, state, info4);
		//@ close [f]this.DedicatedFile(DedicatedFile.class)(fid, null, state, d1, info3);
		//@ close [f]MasterFile(fid, null, state, d1, info2);
		//@ close [f]File(fid, state, info);
	}
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	protected void addSibling(File s) 
  	    //@ requires DedicatedFile(?fileID, ?parentFile, ?activeState, ?siblist, ?info) &*& valid_id(s);
  	    /*@ ensures DedicatedFile(fileID, parentFile, activeState, ?newSibList, info)
  	    		&*& newSibList == (length(siblist) < MAX_SIBLINGS ? append(siblist, cons(s, nil)) : siblist)
  	    		&*& length(siblist) < MAX_SIBLINGS ? mem(s, newSibList) == true : true; @*/
 	{
		
		//@ open DedicatedFile(fileID, parentFile, activeState, siblist, info);
		//@ open MasterFile(fileID, parentFile, activeState, siblist, ?info2);
		super.addSibling(s);
		//@ close MasterFile(fileID, parentFile, activeState, (length(siblist) < MAX_SIBLINGS ? append(siblist, cons(s, nil)) : siblist), info2);
		//@ close DedicatedFile(fileID, parentFile, activeState, (length(siblist) < MAX_SIBLINGS ? append(siblist, cons(s, nil)) : siblist), info);
	}
	
	/*@ lemma void castFileToMaster()
            requires [?f]File(?fid, ?state, ?info);
            ensures switch (info) { case triple(dedFile, siblist, oinfo): return [f]MasterFile(fid, dedFile, state, siblist, oinfo); } ;
	{
	    open [f]File(fid, state, _);
    	}

	lemma void castMasterToFile()
            requires [?f]MasterFile(?fid, ?dedFile, ?state, ?siblist, ?oinfo);
            ensures [f]File(fid, state, triple(dedFile, siblist, oinfo));
	{
	    close [f]File(fid, state, triple(dedFile, siblist, oinfo));
    	}

	lemma void castMasterToDedicated()
            requires [?f]MasterFile(?fid, ?dedFile, ?state, ?siblist, ?oinfo);
            ensures [f]DedicatedFile(fid, dedFile, state, siblist, oinfo);
	{
	    close [f]DedicatedFile(fid, dedFile, state, siblist, oinfo);
    	}

	lemma void castDedicatedToMaster()
            requires [?f]DedicatedFile(?fid, ?dedFile, ?state, ?siblist, ?oinfo);
            ensures [f]MasterFile(fid, dedFile, state, siblist, oinfo);
	{
	    open [f]DedicatedFile(fid, dedFile, state, siblist, oinfo);
    	}

	lemma void castFileToDedicated()
            requires [?f]File(?fid, ?state, ?info);
            ensures switch (info) { case triple(dedFile, siblist, oinfo): return [f]DedicatedFile(fid, dedFile, state, siblist, oinfo); } ;
	{
	    open [f]File(fid, state, _);
	    close [f]DedicatedFile(fid, _, _, _, _);
    	}

	lemma void castDedicatedToFile()
            requires [?f]DedicatedFile(?fid, ?dedFile, ?state, ?siblist, ?oinfo);
            ensures [f]File(fid, state, triple(dedFile, siblist, oinfo));
	{
   	    open [f]DedicatedFile(fid, _, _, _, _);
	    close [f]File(fid, state, triple(dedFile, siblist, oinfo));
    	}
    	@*/
}
