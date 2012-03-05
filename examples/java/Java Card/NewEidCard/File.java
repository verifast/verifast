package be.fedict.neweidapplet;

/*@

inductive triple<a, b, c> = triple(a, b, c);

inductive quad<a, b, c, d> = quad(a, b, c, d);

@*/

public abstract class File {
	/*@ predicate File(short theFileID, boolean activeState, any info) = 
	 	[_]this.fileID |-> theFileID &*& this.active |-> activeState
	 	&*& info == unit; @*/

	// file identifier
	public short fileID;
	protected boolean active;
	
	public File(short fid) 
  	    //@ requires true;
      	    //@ ensures File(fid, true, _) &*& valid_id(this);
    	{
		fileID = fid;
		active = true;
		//@ leak File_fileID(this, _);
		//@ close valid_id(this);
		//@ close File(fid, true, _);
	}
	public short getFileID() 
	    //@ requires [?f]valid_id(this);
	    //@ ensures [f]valid_id(this);
	{
		//@ open [f]valid_id(this);
		return fileID;
		//@ close [f]valid_id(this);
	}
	
	public void setActive(boolean b)
	    //@ requires File(?fid, _, ?info);
	    //@ ensures File(fid, b, info);
	{
		//@ open File(fid, _, info);
		active = b;
		//@ close File(fid, b, info);
	}
	
	/*VF* added because VeriFast can't access protected variables */
	public boolean isActive() 
	    //@ requires [?f]File(?fid, ?state, ?info);
	    //@ ensures [f]File(fid, state, info) &*& result == state;
	{
		//@ open [f]File(fid, state, info);
		return active;
		//@ close [f]File(fid, state, info);
	}
}
