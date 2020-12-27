package be.fedict.neweidapplet;

import javacard.framework.*;

public /*VF*ADDED*/final class ElementaryFile extends File {
	/*@ predicate File(short theFileID, boolean activeState, quad<DedicatedFile, byte[], short, any> info) = 
		ElementaryFile(theFileID, ?dedFile, ?data, activeState, ?sz, ?ifo) &*& info == quad(dedFile, data, sz, ifo); @*/
	/*@ predicate ElementaryFile(short fileID, DedicatedFile parentFile, byte[] data, boolean activeState, short size, any info) = 
		this.File(File.class)(fileID, activeState, _) &*& this.parentFile |-> parentFile &*& 
		this.data |-> data &*& data != null &*& this.size |-> size &*& array_slice(data, 0, data.length, _) &*&
		size >= 0 &*& size <= data.length &*& info == unit &*& data.length <= 30000; @*/
		
	// link to parent DF
	public DedicatedFile parentFile;
	// data stored in file
	private byte[] data;
	// current size of data stored in file
	short size;
	public ElementaryFile(short fid, DedicatedFile parent, byte[] d) 
  	    //@ requires d != null &*& array_slice(d, 0, d.length, _) &*& d.length <= 255 &*& parent != null &*& parent.DedicatedFile(?fileID, ?pf, ?activeState, _, _);
      	    //@ ensures ElementaryFile(fid, parent, d, true, (short)d.length, _);
	{
		super(fid);
		parentFile = parent;
		parent.addSibling(this);
		data = d;
		size = (short) d.length;
		//@ close ElementaryFile(fid, parent, d, true, (short)d.length, _);
	}
	public ElementaryFile(short fid, DedicatedFile parent, short maxSize) 
  	    //@ requires parent != null &*& 30000 >= maxSize &*& maxSize >= 0 &*& parent.DedicatedFile(?fileID, ?pf, ?activeState, ?siblist, ?info) &*& length(siblist) < DedicatedFile.MAX_SIBLINGS;
      	    //@ ensures ElementaryFile(fid, parent, ?data, true, 0, _) &*& data != null &*& data.length == maxSize &*& parent.DedicatedFile(fileID, pf, activeState, append(siblist, cons(this, nil)), info) &*& length(append(siblist, cons(this, nil))) == length(siblist) + 1;
	{
		super(fid);
		parentFile = parent;
		parent.addSibling(this);
		data = new byte[maxSize];
		size = (short) 0;
		//@ close ElementaryFile(fid, parent, data, true, size, _);
		//@ length_append(siblist, cons(this, nil));
	}
	public byte[] getData() 
  	    //@ requires [?f]ElementaryFile(?fid, ?pf, ?d, ?a, ?size, ?info);
      	    //@ ensures [f]ElementaryFile(fid, pf, d, a, size, info) &*& result == d;
	{
		if (active == true) {
			return data;
		} else {
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
			return null; //~allow_dead_code
		}
	}
	public short getCurrentSize() 
  	    //@ requires [?f]ElementaryFile(?fid, ?parent, ?data, ?state, ?thesize, ?info);
      	    //@ ensures [f]ElementaryFile(fid, parent, data, state, thesize, info) &*& result == thesize;
	{	
		//@ open [f]ElementaryFile(fid, parent, data, state, thesize, info);
		//@ open [f]this.File(File.class)(fid, state, ?info2);
		if (active == true) {
			return size;
			//@ close [f]this.File(File.class)(fid, state, info2);
			//@ close [f]ElementaryFile(fid, parent, data, state, thesize, info);
		} else {
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		}
		return 0; //~allow_dead_code
	}
	public short getMaxSize() 
  	    //@ requires [?f]ElementaryFile(?fid, ?parent, ?data, ?state, ?thesize, ?info);
      	    //@ ensures [f]ElementaryFile(fid, parent, data, state, thesize, info) &*& data != null &*& result == data.length &*& data.length <= 30000;
	{
		//@ open [f]ElementaryFile(fid, parent, data, state, thesize, info);
		return (short) this.data.length;
		//@ close [f]ElementaryFile(fid, parent, data, state, thesize, info);
	}
	public void eraseData(short offset) 
  	    //@ requires ElementaryFile(?fid, ?parent, ?theData, ?state, ?thesize, ?info) &*& offset >= 0 &*& offset <= thesize;
      	    //@ ensures ElementaryFile(fid, parent, theData, state, thesize, info);
	{
		//@ open ElementaryFile(fid, parent, theData, state, thesize, info);
		Util.arrayFillNonAtomic(data, offset, (short)(size - offset), (byte) 0);
		//@ close ElementaryFile(fid, parent, theData, state, thesize, info);
	}
	public void updateData(short dataOffset, byte[] newData, short newDataOffset, short length) 
  	    /*@ requires ElementaryFile(?fid, ?parent, ?theData, ?state, ?thesize, ?info) &*& newData != null &*& array_slice(newData, 0, newData.length, _)
  	    		&*& newDataOffset >= 0 &*& length >= 0 &*& newDataOffset + length <= newData.length
  	    		&*& dataOffset >= 0 &*& theData != null &*& dataOffset + length <= theData.length; @*/
      	    /*@ ensures ElementaryFile(fid, parent, theData, state, (short)(dataOffset + length), info) &*& array_slice(newData, 0, newData.length, _); @*/
	{
		//@ open ElementaryFile(fid, parent, theData, state, thesize, info);
		// update size
		size = (short) (dataOffset + length);
		// copy new data
		Util.arrayCopy(newData, newDataOffset, data, dataOffset, length);
		//@ close ElementaryFile(fid, parent, theData, state, (short)(dataOffset + length), info);
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
		//@ open ElementaryFile(fid, _, _, _, _, ?info2);
		super.setActive(b);
		//@ close ElementaryFile(fid, _, _, _, _, info2);
		//@ close File(fid, _, info);
	}
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public boolean isActive() 
	    //@ requires [?f]File(?fid, ?state, ?info);
	    //@ ensures [f]File(fid, state, info) &*& result == state;
	{
		//@ open [f]File(fid, _, info);
		//@ open [f]ElementaryFile(fid, _, _, _, _, ?info2);
		boolean b = super.isActive();
		//@ close [f]ElementaryFile(fid, _, _, _, _, info2);
		//@ close [f]File(fid, _, info);
		return b;
	}
	
	/*@
	lemma void castFileToElementary()
            requires [?f]File(?fid, ?state, ?info);
            ensures switch(info) { case quad(dedFile, dta, sz, ifo) : return [f]ElementaryFile(fid, dedFile, dta, state, sz, ifo); };
	{
	    open [f]File(fid, state, info);
    	}

	lemma void castElementaryToFile()
            requires [?f]ElementaryFile(?fid, ?dedFile, ?dta, ?state, ?sz, ?ifo);
            ensures [f]File(fid, state, quad(dedFile, dta, sz, ifo));
	{
	    close [f]File(fid, state, quad(dedFile, dta, sz, ifo));
    	}
    	
    	lemma void neq(ElementaryFile other)
    	  requires ElementaryFile(?fid, ?dedFile, ?dta, ?state, ?sz, ?ifo) &*& other.ElementaryFile(?fid2, ?dedFile2, ?dta2, ?state2, ?sz2, ?ifo2);
    	  ensures ElementaryFile(fid, dedFile, dta, state, sz, ifo) &*& other.ElementaryFile(fid2, dedFile2, dta2, state2, sz2, ifo2) &*& this != other;
    	{
    	  open ElementaryFile(fid, dedFile, dta, state, sz, ifo);
    	  open other.ElementaryFile(fid2, dedFile2, dta2, state2, sz2, ifo2);
    	}
    	@*/
}
