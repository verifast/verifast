// Note: on this program, VeriFast/Redux is much faster than VeriFast/Z3! (2s versus 70s). To use Redux, use:
//   vfide -prover redux EidCard.java
//   verifast -c -prover redux EidCard.java

/*
                           
                                         @@@@                                
                                     @@@@@@@@@@@                             
                                @@@@@@@@@@@@@@@@@@@@@                        
                          @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@                  
                @@@@@@@@@@@@@@@@@@@@@@@@.....@@@@@@@@@@@@@@@@@@@@@@@@@       
                @@@@@@@@@@@@@@@@@@@@.............@@@@@@@@@@@@@@@@@@@@@       
                @@@@@@@@@@@@@@.........................@@@@@@@@@@@@@@@       
                @@@@@............................................@@@@@       
                @@@@@............................................@@@@        
                @@@@@............................................@@@@        
                 @@@@............................................@@@@        
                 @@@@......::::.................::::::::::::.....@@@@        
                 @@@@......'@@@,...............'@@@@@@@@@@@@,...@@@@@        
                  @@@@......#@@@..............:@@@,.............@@@@         
                  @@@@.......@@@#.............@@@'..............@@@@         
                  @@@@.......,@@@;...........#@@#..............@@@@@         
                   @@@@.......;@@@..........'@@@@@@@@@+........@@@@          
                   @@@@........+@@@........:@@@''''''';........@@@@          
                    @@@@........@@@+.......@@@:...............@@@@           
                    @@@@.........@@@,.....#@@'................@@@@           
                     @@@@........,@@@....'@@#................@@@@            
                      @@@@........'@@#..,@@@................@@@@             
                      @@@@.........#@@;.@@@................@@@@              
                       @@@@.........@@@+@@:...............@@@@@              
                        @@@@........,@@@@+...............@@@@@               
                         @@@@@..........................@@@@@                
                          @@@@@........................@@@@@                 
                           @@@@@......................@@@@                   
                             @@@@@..................@@@@@                    
                              @@@@@@..............@@@@@@                     
                                @@@@@@..........@@@@@@                       
                                 @@@@@@@......@@@@@@                         
                                   @@@@@@@@@@@@@@@                           
                                      @@@@@@@@@@
                                      
                                Powered by VeriFast (c)
*/


/*
 * Quick-Key Toolset Project.
 * Copyright (C) 2010 FedICT.
 *
 * This is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License version
 * 3.0 as published by the Free Software Foundation.
 *
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this software; if not, see 
 * http://www.gnu.org/licenses/.
 */
package be.fedict.eidapplet;

import javacard.security.KeyPair;
import javacard.security.RSAPrivateKey;
import javacard.security.RSAPrivateCrtKey;
import javacard.security.RSAPublicKey;
import javacard.security.RandomData;
import javacardx.crypto.Cipher;
import org.globalplatform.GPSystem;

/*VF*ADDED FOLLOWING IMPORTS*/
import javacard.framework.Applet;
import javacard.framework.*;
import javacard.security.PrivateKey;
import javacard.security.PublicKey;
/*VF*ADDED FOLLOWING CLASSES*/

/*@

inductive triple<a, b, c> = triple(a, b, c);

inductive quad<a, b, c, d> = quad(a, b, c, d);

@*/

public abstract class File {
	/*@ predicate File(short theFileID, boolean activeState, any info) = 
	 	[_]this.fileID |-> theFileID &*& this.active |-> activeState
	 	&*& info == unit; @*/

	// file identifier
	private short fileID;
	protected boolean active;
	
	public File(short fid) 
  	    //@ requires true;
      	    //@ ensures File(fid, true, _) &*& valid_id(this);
    	{
		fileID = fid;
		active = true;
		//@ leak File_fileID(this, _);
		////@ close valid_id(this); // auto
		////@ close File(fid, true, _); // auto
	}
	public short getFileID() 
	    //@ requires [?f]valid_id(this);
	    //@ ensures [f]valid_id(this);
	{
		////@ open [f]valid_id(this); // auto
		return fileID;
		//@ close [f]valid_id(this); // todo
	}
	
	public void setActive(boolean b)
	    //@ requires File(?fid, _, ?info);
	    //@ ensures File(fid, b, info);
	{
		////@ open File(fid, _, info); // auto
		active = b;
		////@ close File(fid, b, info); // auto
	}
	
	/*VF* added because VeriFast can't access protected variables */
	public boolean isActive() 
	    //@ requires [?f]File(?fid, ?state, ?info);
	    //@ ensures [f]File(fid, state, info) &*& result == state;
	{
		////@ open [f]File(fid, state, info); // auto
		return active;
		////@ close [f]File(fid, state, info); // auto
	}
}

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
	private DedicatedFile parentFile;
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
		////@ close foreachp(nil, valid_id); // auto
		////@ close DedicatedFile(fid, null, true, nil, _); // auto
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
		////@ close foreachp(nil, valid_id); // auto
		////@ close DedicatedFile(fid, parent, true, nil, _); // auto
	}
	public DedicatedFile getParent() 
	    //@ requires DedicatedFile(?fid, ?parentfile, ?active, ?siblist, ?info);
	    //@ ensures DedicatedFile(fid, parentfile, active, siblist, info) &*& result == parentfile;
	{
		////@ open DedicatedFile(fid, parentfile, active, siblist, info); // auto
		return parentFile;
		////@ close DedicatedFile(fid, parentfile, active, siblist, info); // auto
	}
	
	protected void addSibling(File s) 
  	    //@ requires DedicatedFile(?fileID, ?parentFile, ?activeState, ?siblist, ?info) &*& valid_id(s);
  	    /*@ ensures DedicatedFile(fileID, parentFile, activeState, ?newSibList, info)
  	    		&*& newSibList == (length(siblist) < MAX_SIBLINGS ? append(siblist, cons(s, nil)) : siblist)
  	    		&*& length(siblist) < MAX_SIBLINGS ? mem(s, newSibList) == true : true; @*/
	{
                ////@ open DedicatedFile(fileID, parentFile, activeState, siblist, info); // auto
		if (number < MAX_SIBLINGS) {
			//@ assert array_slice(?thesiblings, _, _, ?sb);
			siblings[number++] = s;
			//@ take_one_more(length(siblist), update(length(siblist), s, sb));
			//@ assert array_slice(thesiblings, _, _, ?sb2);
			////@ close foreachp(nil, valid_id); // auto
			//@ close foreachp(cons(s, nil), valid_id);
			//@ foreachp_append(take(length(siblist), sb), cons(s, nil));	
		}
		
		///*@ close DedicatedFile(fileID, parentFile, activeState,		 // auto
		//	snumber < MAX_SIBLINGS ? append(take(snumber, siblist), cons(s, nil)) : siblist, 
		//	info); @*/
	}

	public File getSibling(short fid) 
  	    //@ requires [?f]DedicatedFile(?fileID, ?parentFile, ?activeState, ?siblist, ?info);
      	    //@ ensures [f]DedicatedFile(fileID, parentFile, activeState, siblist, info) &*& result == null ? true : mem(result, siblist) == true;
	{
		//@ open DedicatedFile(fileID, parentFile, activeState, siblist, info); // todo (by allowing patterns in wanted terms)
		//@ assert [f]array_slice(?thesiblings, _, _, ?sb);
		//@ int snumber = length(siblist);
		for (byte i = 0; i < number; i++) 
		/*@ invariant i >= 0 &*& [f]this.File(File.class)(fileID, activeState, _) &*& [f]this.parentFile |-> parentFile &*& [f]number |-> (byte) length(siblist) &*& [f]this.siblings |-> thesiblings &*& [f]array_slice(thesiblings, 0, thesiblings.length, sb)
		      &*& [f]foreachp(siblist, valid_id); @*/
		{
			File fl = siblings[i];
			//@ nth_take(i, snumber, sb);
			//@ foreachp_remove<File>(fl, siblist);
			if (fl != null && fl.getFileID() == fid) {
				//@ foreachp_unremove<File>(fl, siblist);
				return fl;
				////@ close [f]DedicatedFile(fileID, parentFile, activeState, siblist, info); // auto
			}
			//@ foreachp_unremove<File>(fl, siblist);
		}
		////@ close [f]DedicatedFile(fileID, parentFile, activeState, siblist, info); // auto
		return null;
	}

        /*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public short getFileID() 
	    //@ requires [?f]valid_id(this);
	    //@ ensures [f]valid_id(this);
	{
		////@ open [f]valid_id(this); // auto
		File thiz = this;
		return fileID;
		//@ close [f]valid_id(this); // todo
	}
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public void setActive(boolean b)
	    //@ requires File(?fid, _, ?info);
	    //@ ensures File(fid, b, info);
	{
		////@ open File(fid, _, info); // auto
		////@ open DedicatedFile(fid, ?d1, _, ?siblist, ?info2); // auto
		File thiz = this;
		////@ open thiz.File(fid, _, ?info3); // auto
		active = b;
		////@ close thiz.File(fid, b, info3); // auto
		////@ close DedicatedFile(fid, d1, b, siblist, info2); // auto
		////@ close File(fid, b, info); // auto
	}
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public boolean isActive() 
	    //@ requires [?f]File(?fid, ?state, ?info);
	    //@ ensures [f]File(fid, state, info) &*& result == state;
	{
		////@ open [f]File(fid, state, info); // auto
		////@ open [f]DedicatedFile(fid, ?d1, state, ?siblist, ?info2); // auto
		////@ open this.File(File.class)(fid, state, ?info3); // auto
		return active;
		////@ close [f]this.File(File.class)(fid, state, info3); // auto
		////@ close [f]DedicatedFile(fid, d1, state, siblist, info2); // auto
		////@ close [f]File(fid, state, info); // auto
	}
	
	/*@ 
	lemma void castFileToDedicated()
            requires [?f]File(?fid, ?state, ?info);
            ensures switch (info) { case triple(dedFile, siblist, oinfo): return [f]DedicatedFile(fid, dedFile, state, siblist, oinfo); } ;
	{
	   // open [f]File(fid, state, _); // auto
    	}

	lemma void castDedicatedToFile()
            requires [?f]DedicatedFile(?fid, ?dedFile, ?state, ?siblist, ?oinfo);
            ensures [f]File(fid, state, triple(dedFile, siblist, oinfo));
	{
	   // close [f]File(fid, state, triple(dedFile, siblist, oinfo)); // auto
    	}
    	@*/
}

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
		////@ close MasterFile(0x3F00, null, true, _, _); // auto
	}
	
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public DedicatedFile getParent() 
	    //@ requires DedicatedFile(?fid, ?parentfile, ?active, ?siblist, ?info);
	    //@ ensures DedicatedFile(fid, parentfile, active, siblist, info) &*& result == parentfile;
	{
		////@ open DedicatedFile(fid, parentfile, active, siblist, info); // auto
		////@ open MasterFile(fid, parentfile, active, siblist, ?info2); // auto
		////@ open this.DedicatedFile(DedicatedFile.class)(fid, parentfile, active, siblist, ?info3); // auto
		return parentFile;
		////@ close this.DedicatedFile(DedicatedFile.class)(fid, parentfile, active, siblist, info3); // auto
		////@ close MasterFile(fid, parentfile, active, siblist, info2); // auto
		////@ close DedicatedFile(fid, parentfile, active, siblist, info); // auto
	}

	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public File getSibling(short fid) 
  	    //@ requires [?f]DedicatedFile(?fileID, ?parentFile, ?activeState, ?siblist, ?info);
      	    //@ ensures [f]DedicatedFile(fileID, parentFile, activeState, siblist, info) &*& result == null ? true : mem(result, siblist) == true;
	{
		///@ open [f]DedicatedFile(fileID, parentFile, activeState, siblist, info); // auto
		////@ open [f]MasterFile(fileID, parentFile, activeState, siblist, info); // auto
		return super.getSibling(fid);
		////@ close [f]MasterFile(fileID, parentFile, activeState, siblist, info); // auto
		////@ close [f]DedicatedFile(fileID, parentFile, activeState, siblist, info); // todo
	}
	
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public short getFileID() 
	    //@ requires [?f]valid_id(this);
	    //@ ensures [f]valid_id(this);
	{
		////@ open [f]valid_id(this); // auto
		return fileID;
		//@ close [f]valid_id(this);
	}
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public void setActive(boolean b)
	    //@ requires File(?fid, _, ?info);
	    //@ ensures File(fid, b, info);
	{
		////@ open File(fid, _, info); // auto
		////@ open MasterFile(fid, ?d0, _, ?d1, ?info2); // auto
		////@ open this.DedicatedFile(DedicatedFile.class)(fid, null, _, d1, ?info3); // auto
		////@ open this.File(File.class)(fid, _, ?info4); // auto
		active = b;
		////@ close this.File(File.class)(fid, b, info4); // auto
		////@ close this.DedicatedFile(DedicatedFile.class)(fid, null, b, d1, info3); // auto
		////@ close MasterFile(fid, null, b, d1, info2); // auto
		////@ close File(fid, b, info); // auto
	}
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public boolean isActive() 
	    //@ requires [?f]File(?fid, ?state, ?info);
	    //@ ensures [f]File(fid, state, info) &*& result == state;
	{
		////@ open [f]File(fid, state, info); // auto
		////@ open [f]MasterFile(fid, ?d0, state, ?d1, ?info2); // auto
		////@ open [f]this.DedicatedFile(DedicatedFile.class)(fid, null, state, d1, ?info3); // auto
		////@ open [f]this.File(File.class)(fid, state, ?info4); // auto
		return active;
		////@ close [f]this.File(File.class)(fid, state, info4); // auto
		////@ close [f]this.DedicatedFile(DedicatedFile.class)(fid, null, state, d1, info3); // auto
		////@ close [f]MasterFile(fid, null, state, d1, info2); // auto
		////@ close [f]File(fid, state, info); // auto
	}
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	protected void addSibling(File s) 
  	    //@ requires DedicatedFile(?fileID, ?parentFile, ?activeState, ?siblist, ?info) &*& valid_id(s);
  	    /*@ ensures DedicatedFile(fileID, parentFile, activeState, ?newSibList, info)
  	    		&*& newSibList == (length(siblist) < MAX_SIBLINGS ? append(siblist, cons(s, nil)) : siblist)
  	    		&*& length(siblist) < MAX_SIBLINGS ? mem(s, newSibList) == true : true; @*/
 	{
		
		////@ open DedicatedFile(fileID, parentFile, activeState, siblist, info); // auto
		////@ open MasterFile(fileID, parentFile, activeState, siblist, ?info2); // auto
		super.addSibling(s);
		////@ close MasterFile(fileID, parentFile, activeState, (length(siblist) < MAX_SIBLINGS ? append(siblist, cons(s, nil)) : siblist), info2); // auto
		////@ close DedicatedFile(fileID, parentFile, activeState, (length(siblist) < MAX_SIBLINGS ? append(siblist, cons(s, nil)) : siblist), info);
	}
	
	/*@ lemma void castFileToMaster()
            requires [?f]File(?fid, ?state, ?info);
            ensures switch (info) { case triple(dedFile, siblist, oinfo): return [f]MasterFile(fid, dedFile, state, siblist, oinfo); } ;
	{
	   // open [f]File(fid, state, _);
    	}

	lemma void castMasterToFile()
            requires [?f]MasterFile(?fid, ?dedFile, ?state, ?siblist, ?oinfo);
            ensures [f]File(fid, state, triple(dedFile, siblist, oinfo));
	{
	   // close [f]File(fid, state, triple(dedFile, siblist, oinfo));
    	}

	lemma void castMasterToDedicated()
            requires [?f]MasterFile(?fid, ?dedFile, ?state, ?siblist, ?oinfo);
            ensures [f]DedicatedFile(fid, dedFile, state, siblist, oinfo);
	{
	   // close [f]DedicatedFile(fid, dedFile, state, siblist, oinfo); // auto
    	}

	lemma void castDedicatedToMaster()
            requires [?f]DedicatedFile(?fid, ?dedFile, ?state, ?siblist, ?oinfo);
            ensures [f]MasterFile(fid, dedFile, state, siblist, oinfo);
	{
	   // open [f]DedicatedFile(fid, dedFile, state, siblist, oinfo); // auto
    	}

	lemma void castFileToDedicated()
            requires [?f]File(?fid, ?state, ?info);
            ensures switch (info) { case triple(dedFile, siblist, oinfo): return [f]DedicatedFile(fid, dedFile, state, siblist, oinfo); } ;
	{
	  // open [f]File(fid, state, _); // auto
	    close [f]DedicatedFile(fid, _, _, _, _); // todo
    	}

	lemma void castDedicatedToFile()
            requires [?f]DedicatedFile(?fid, ?dedFile, ?state, ?siblist, ?oinfo);
            ensures [f]File(fid, state, triple(dedFile, siblist, oinfo));
	{
   	  //  open [f]DedicatedFile(fid, _, _, _, _); // auto
	    close [f]File(fid, state, triple(dedFile, siblist, oinfo)); // todo
    	}
    	@*/
}

public /*VF*ADDED*/final class ElementaryFile extends File {
	/*@ predicate File(short theFileID, boolean activeState, quad<DedicatedFile, byte[], short, any> info) = 
		ElementaryFile(theFileID, ?dedFile, ?data, activeState, ?sz, ?ifo) &*& info == quad(dedFile, data, sz, ifo); @*/
	/*@ predicate ElementaryFile(short fileID, DedicatedFile parentFile, byte[] data, boolean activeState, short size, any info) = 
		this.File(File.class)(fileID, activeState, _) &*& this.parentFile |-> parentFile &*& 
		this.data |-> data &*& data != null &*& this.size |-> size &*& array_slice(data, 0, data.length, _) &*&
		size >= 0 &*& size <= data.length &*& info == unit &*& data.length <= Short.MAX_VALUE; @*/
		
	// link to parent DF
	private DedicatedFile parentFile;
	// data stored in file
	private byte[] data;
	// current size of data stored in file
	short size;
	public ElementaryFile(short fid, DedicatedFile parent, byte[] d) 
  	    //@ requires d != null &*& array_slice(d, 0, d.length, _) &*& d.length <= Short.MAX_VALUE &*& parent != null &*& parent.DedicatedFile(?fileID, ?pf, ?activeState, _, _);
      	    //@ ensures ElementaryFile(fid, parent, d, true, (short)d.length, _);
	{
		super(fid);
		parentFile = parent;
		parent.addSibling(this);
		data = d;
		size = (short) d.length;
		// //@ close ElementaryFile(fid, parent, d, true, (short)d.length, _); // auto
	}
	public ElementaryFile(short fid, DedicatedFile parent, short maxSize) 
  	    //@ requires parent != null &*& maxSize >= 0 &*& parent.DedicatedFile(?fileID, ?pf, ?activeState, ?siblist, ?info) &*& length(siblist) < DedicatedFile.MAX_SIBLINGS;
      	    //@ ensures ElementaryFile(fid, parent, ?data, true, 0, _) &*& data != null &*& data.length == maxSize &*& parent.DedicatedFile(fileID, pf, activeState, append(siblist, cons(this, nil)), info) &*& length(append(siblist, cons(this, nil))) == length(siblist) + 1;
	{
		super(fid);
		parentFile = parent;
		parent.addSibling(this);
		data = new byte[maxSize];
		size = (short) 0;
		//@ length_append(siblist, cons(this, nil));
		// //@ close ElementaryFile(fid, parent, data, true, size, _); // auto
	}
	public byte[] getData() 
  	    //@ requires [?f]ElementaryFile(?fid, ?pf, ?d, ?a, ?size, ?info);
      	    //@ ensures [f]ElementaryFile(fid, pf, d, a, size, info) &*& result == d;
	{
		if (active == true) {
			return data;
		} else {
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
			////@ close [f]ElementaryFile(fid, pf, d, a, size); // auto
			return null; //~allow_dead_code
		}
	}
	public short getCurrentSize() 
  	    //@ requires [?f]ElementaryFile(?fid, ?parent, ?data, ?state, ?thesize, ?info);
      	    //@ ensures [f]ElementaryFile(fid, parent, data, state, thesize, info) &*& result == thesize;
	{	
		////@ open [f]ElementaryFile(fid, parent, data, state, thesize, info); // auto
		////@ open [f]this.File(File.class)(fid, state, ?info2); // auto
		if (active == true) {
			return size;
			////@ close [f]this.File(File.class)(fid, state, info2); // auto
			////@ close [f]ElementaryFile(fid, parent, data, state, thesize, info); // auto
		} else {
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		}
	}
	public short getMaxSize() 
  	    //@ requires [?f]ElementaryFile(?fid, ?parent, ?data, ?state, ?thesize, ?info);
      	    //@ ensures [f]ElementaryFile(fid, parent, data, state, thesize, info) &*& data != null &*& result == data.length;
	{
		////@ open [f]ElementaryFile(fid, parent, data, state, thesize, info); // auto
		return (short) this.data.length;
		////@ close [f]ElementaryFile(fid, parent, data, state, thesize, info); // auto
	}
	public void eraseData(short offset) 
  	    //@ requires ElementaryFile(?fid, ?parent, ?theData, ?state, ?thesize, ?info) &*& offset >= 0 &*& offset <= thesize;
      	    //@ ensures ElementaryFile(fid, parent, theData, state, thesize, info);
	{
		////@ open ElementaryFile(fid, parent, theData, state, thesize, info); // auto
		Util.arrayFillNonAtomic(data, offset, (short)(size - offset), (byte) 0);
		////@ close ElementaryFile(fid, parent, theData, state, thesize, info); // auto
	}
	public void updateData(short dataOffset, byte[] newData, short newDataOffset, short length) 
  	    /*@ requires ElementaryFile(?fid, ?parent, ?theData, ?state, ?thesize, ?info) &*& newData != null &*& array_slice(newData, 0, newData.length, _)
  	    		&*& newDataOffset >= 0 &*& length >= 0 &*& newDataOffset + length <= newData.length
  	    		&*& dataOffset >= 0 &*& theData != null &*& dataOffset + length <= theData.length; @*/
      	    /*@ ensures ElementaryFile(fid, parent, theData, state, (short)(dataOffset + length), info) &*& array_slice(newData, 0, newData.length, _); @*/
	{
		//@ open ElementaryFile(fid, parent, theData, state, thesize, info); // todo 
		// update size
		size = (short) (dataOffset + length);
		// copy new data
		Util.arrayCopy(newData, newDataOffset, data, dataOffset, length);
		////@ close ElementaryFile(fid, parent, theData, state, (short)(dataOffset + length), info); // auto
	}

	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public short getFileID() 
	    //@ requires [?f]valid_id(this);
	    //@ ensures [f]valid_id(this);
	{
		////@ open [f]valid_id(this); // auto
		return fileID;
		//@ close [f]valid_id(this);
	}
	
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public void setActive(boolean b)
	    //@ requires File(?fid, _, ?info);
	    //@ ensures File(fid, b, info);
	{
		////@ open File(fid, _, info); // auto
		////@ open ElementaryFile(fid, _, _, _, _, ?info2); // auto
		super.setActive(b);
		////@ close ElementaryFile(fid, _, _, _, _, info2); // auto
		////@ close File(fid, _, info); // auto
	}
	
	/*VF* METHODE ERBIJ GEZET VOOR VERIFAST */
	public boolean isActive() 
	    //@ requires [?f]File(?fid, ?state, ?info);
	    //@ ensures [f]File(fid, state, info) &*& result == state;
	{
		////@ open [f]File(fid, _, info); // auto
		////@ open [f]ElementaryFile(fid, _, _, _, _, ?info2); // auto
		boolean b = super.isActive();
		////@ close [f]ElementaryFile(fid, _, _, _, _, info2); // auto
		////@ close [f]File(fid, _, info); // auto
		return b;
	}
	
	/*@
	lemma void castFileToElementary()
            requires [?f]File(?fid, ?state, ?info);
            ensures switch(info) { case quad(dedFile, dta, sz, ifo) : return [f]ElementaryFile(fid, dedFile, dta, state, sz, ifo); };
	{
	    //open [f]File(fid, state, info); // auto
    	}

	lemma void castElementaryToFile()
            requires [?f]ElementaryFile(?fid, ?dedFile, ?dta, ?state, ?sz, ?ifo);
            ensures [f]File(fid, state, quad(dedFile, dta, sz, ifo));
	{
	    //close [f]File(fid, state, quad(dedFile, dta, sz, ifo)); // auto
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

/*VF*DONE ADDING CLASSES*/

/*@
  predicate array_pointer(byte[] buffer, short length) =
    buffer == null ?
      true
    :
      array_slice(buffer, 0, buffer.length, _) &*& buffer.length == length;

  predicate transient_array_pointer(byte[] buffer, short length;) =
    buffer == null ?
      true
    :
      array_slice(buffer, 0, buffer.length, _) &*& buffer.length == length &*& is_transient_byte_array(buffer) == true;

  predicate selected_file_types(File theSelectedFile, MasterFile theMasterFile, DedicatedFile theBelpicDirectory, DedicatedFile theIdDirectory, ElementaryFile theIdentityFile, ElementaryFile theIdentityFileSignature, ElementaryFile theAddressFile, ElementaryFile theAddressFileSignature, ElementaryFile thePhotoFile, 
	  ElementaryFile thecaRoleIDFile, ElementaryFile theDirFile, ElementaryFile theTokenInfo, ElementaryFile theObjectDirectoryFile, ElementaryFile theAuthenticationObjectDirectoryFile, ElementaryFile thePrivateKeyDirectoryFile, ElementaryFile theCaCertificate, ElementaryFile theCertificateDirectoryFile, ElementaryFile theRrnCertificate, ElementaryFile theRootCaCertificate, ElementaryFile theAuthenticationCertificate, ElementaryFile theNonRepudationCertificate, ElementaryFile thePreferencesFile; ElementaryFile theSelectedFile2) = 
	    theSelectedFile == theMasterFile || theSelectedFile == theBelpicDirectory || theSelectedFile == theIdDirectory ? theSelectedFile2 == null : 
	      theSelectedFile == theIdentityFile ? theSelectedFile2 == theIdentityFile : 
	        theSelectedFile == theIdentityFileSignature ? theSelectedFile2 == theIdentityFileSignature : 
	          theSelectedFile == theAddressFile ? theSelectedFile2 == theAddressFile : 
	            theSelectedFile == theAddressFileSignature ? theSelectedFile2 == theAddressFileSignature : 
	              theSelectedFile == thePhotoFile ? theSelectedFile2 == thePhotoFile : 
	                theSelectedFile == thecaRoleIDFile ? theSelectedFile2 == thecaRoleIDFile : 
	                  theSelectedFile == theDirFile ? theSelectedFile2 == theDirFile : 
	                    theSelectedFile == theTokenInfo ? theSelectedFile2 == theTokenInfo : 
	                      theSelectedFile == theObjectDirectoryFile ? theSelectedFile2 == theObjectDirectoryFile : 
	                        theSelectedFile == theAuthenticationObjectDirectoryFile ? theSelectedFile2 == theAuthenticationObjectDirectoryFile : 
 	                          theSelectedFile == thePrivateKeyDirectoryFile ? theSelectedFile2 == thePrivateKeyDirectoryFile : 
                                    theSelectedFile == theCaCertificate ? theSelectedFile2 == theCaCertificate :
                                      theSelectedFile == theRrnCertificate ? theSelectedFile2 == theRrnCertificate :
                                        theSelectedFile == theRootCaCertificate ? theSelectedFile2 == theRootCaCertificate :
                                          theSelectedFile == theAuthenticationCertificate ? theSelectedFile2 == theAuthenticationCertificate :
                                            theSelectedFile == theNonRepudationCertificate ? theSelectedFile2 == theNonRepudationCertificate :
                                              theSelectedFile == thePreferencesFile ? theSelectedFile2 == thePreferencesFile :
                                                (theSelectedFile == theCertificateDirectoryFile &*& theSelectedFile2 == theCertificateDirectoryFile);

@*/

//@ predicate eq<T>(T t1; T t2) = t2 == t1;

public final class EidCard extends Applet {
	/*@
	
          predicate valid() =
            randomBuffer |-> ?theRandomBuffer &*& theRandomBuffer != null &*& array_slice(theRandomBuffer, 0, theRandomBuffer.length, _) &*& theRandomBuffer.length == 256 &*&
            responseBuffer |-> ?theResponseBuffer &*& theResponseBuffer != null &*& array_slice(theResponseBuffer, 0, theResponseBuffer.length, _) &*& theResponseBuffer.length == 128 &*&
            randomData |-> ?theRandomData &*& theRandomData != null &*&
            cipher |-> ?theCipher &*& theCipher != null &*&
            messageBuffer |-> ?theMessageBuffer &*& theMessageBuffer != null &*& theMessageBuffer.length == 128 &*& is_transient_byte_array(theMessageBuffer) == true &*&
            previousApduType |-> ?thePreviousApduType &*& thePreviousApduType != null &*& thePreviousApduType.length == 1 &*& is_transient_byte_array(thePreviousApduType) == true &*&
            signatureType |-> ?theSignatureType &*& theSignatureType != null &*& theSignatureType.length == 1 &*& is_transient_byte_array(theSignatureType) == true &*&
            masterFile |-> ?theMasterFile &*& theMasterFile.MasterFile(0x3F00, null, _, ?masterSibs, _) &*& theMasterFile != null &*& theMasterFile.getClass() == MasterFile.class &*&
            cardholderPin |-> ?theCardholderPin &*& OwnerPIN(theCardholderPin, _, _) &*& theCardholderPin != null &*& 
            resetPin |-> ?theResetPin &*& OwnerPIN(theResetPin, _, _) &*& theResetPin != null &*&
            unblockPin |-> ?theUnblockPin &*& OwnerPIN(theUnblockPin, _, _) &*& theUnblockPin != null &*&
            activationPin |-> ?theActivationPin &*& OwnerPIN(theActivationPin, _, _) &*& theActivationPin != null &*&
            identityFile |-> ?theIdentityFile &*& theIdentityFile.ElementaryFile(_, _, ?identityData, _, _, _) &*& theIdentityFile != null &*& identityData != null &*& identityData.length == 0xD0 &*& theIdentityFile.getClass() == ElementaryFile.class &*&
            identityFileSignature |-> ?theIdentityFileSignature &*& theIdentityFileSignature.ElementaryFile(_, _, ?theIdentityFileSignatureData, _, _, _) &*& theIdentityFileSignature != null &*& theIdentityFileSignatureData != null &*& theIdentityFileSignatureData.length == 0x80 &*& theIdentityFileSignature.getClass() == ElementaryFile.class &*&
            addressFile |-> ?theAddressFile &*& theAddressFile.ElementaryFile(_, _, ?theAddressFileData, _, _, _) &*& theAddressFile != null &*& theAddressFileData != null &*& theAddressFileData.length == 117 &*& theAddressFile.getClass() == ElementaryFile.class &*&
            addressFileSignature |-> ?theAddressFileSignature &*& theAddressFileSignature.ElementaryFile(_, _, ?theAddressFileSignatureData, _, _, _) &*& theAddressFileSignature != null &*& theAddressFileSignatureData != null &*& theAddressFileSignatureData.length == 128 &*& theAddressFileSignature.getClass() == ElementaryFile.class &*&
            photoFile |-> ?thePhotoFile &*& thePhotoFile.ElementaryFile(_, _, _, _, _, _) &*& thePhotoFile != null &*& thePhotoFile.getClass() == ElementaryFile.class &*&
            caRoleIDFile |-> ?thecaRoleIDFile &*& thecaRoleIDFile.ElementaryFile(_, _, ?theCaRoleIDFileData, _, _, _) &*& thecaRoleIDFile != null &*& theCaRoleIDFileData != null &*& theCaRoleIDFileData.length == 0x20 &*& thecaRoleIDFile.getClass() == ElementaryFile.class &*&
            dirFile |-> ?theDirFile &*& theDirFile.ElementaryFile(_, _, ?theDirFileData, _, _, _) &*& theDirFile != null &*& theDirFileData != null &*& theDirFileData.length ==  0x25 &*& theDirFile.getClass() == ElementaryFile.class &*&
            tokenInfo |-> ?theTokenInfo &*& theTokenInfo.ElementaryFile(_, _, ?theTokenInfoData, _, _, _) &*& theTokenInfo != null &*& theTokenInfoData != null &*& theTokenInfoData.length == 0x30 &*& theTokenInfo.getClass() == ElementaryFile.class &*&
            objectDirectoryFile |-> ?theObjectDirectoryFile &*& theObjectDirectoryFile.ElementaryFile(_, _, ?theObjectDirectoryFileData, _, _, _) &*& theObjectDirectoryFile != null &*& theObjectDirectoryFileData != null &*& theObjectDirectoryFileData.length == 40 &*& theObjectDirectoryFile.getClass() == ElementaryFile.class &*&
            authenticationObjectDirectoryFile |-> ?theAuthenticationObjectDirectoryFile &*& theAuthenticationObjectDirectoryFile.ElementaryFile(_, _, ?theAuthenticationObjectDirectoryFileData, _, _, _) &*& theAuthenticationObjectDirectoryFile != null &*& theAuthenticationObjectDirectoryFileData != null &*& theAuthenticationObjectDirectoryFileData.length == 0x40 &*&  theAuthenticationObjectDirectoryFile.getClass() == ElementaryFile.class &*&
            privateKeyDirectoryFile |-> ?thePrivateKeyDirectoryFile &*& thePrivateKeyDirectoryFile.ElementaryFile(_, _, ?thePrivateKeyDirectoryFileData, _, _, _) &*& thePrivateKeyDirectoryFile != null &*& thePrivateKeyDirectoryFileData != null &*& thePrivateKeyDirectoryFileData.length == 0xB0 &*& thePrivateKeyDirectoryFile.getClass() == ElementaryFile.class &*&
            certificateDirectoryFile |-> ?theCertificateDirectoryFile &*& theCertificateDirectoryFile.ElementaryFile(_, _, ?theCertificateDirectoryFileData, _, _, _) &*& theCertificateDirectoryFile != null &*& theCertificateDirectoryFileData != null &*& theCertificateDirectoryFileData.length == 0xB0 &*& theCertificateDirectoryFile.getClass() == ElementaryFile.class &*&
            belpicDirectory |-> ?theBelpicDirectory &*& theBelpicDirectory.DedicatedFile(_, _, _, ?belpicSibs, _) &*& theBelpicDirectory != null &*& theBelpicDirectory.getClass() == DedicatedFile.class &*&
            idDirectory |-> ?theIdDirectory &*& theIdDirectory.DedicatedFile(_, _, _, ?idSibs, _) &*& theIdDirectory != null &*& theIdDirectory.getClass() == DedicatedFile.class &*&
            caCertificate |-> ?theCaCertificate &*& theCaCertificate.ElementaryFile(_, _, _, _, _, _) &*& theCaCertificate.getClass() == ElementaryFile.class &*&
	    selectedFile |-> ?theSelectedFile &*& theSelectedFile != null &*&
	    masterSibs == cons<File>(theDirFile, cons(theBelpicDirectory, cons(theIdDirectory, nil))) &*&
	    rootCaCertificate |-> ?theRootCaCertificate &*& theRootCaCertificate.ElementaryFile(_, _, _, _, _, _) &*& theRootCaCertificate.getClass() == ElementaryFile.class &*&
	    rrnCertificate |-> ?theRrnCertificate &*& theRrnCertificate.ElementaryFile(_, _, _, _, _, _) &*& theRrnCertificate.getClass() == ElementaryFile.class &*&
	    authenticationCertificate |-> ?theAuthenticationCertificate &*& theAuthenticationCertificate.ElementaryFile(_, _, _, _, _, _) &*& theAuthenticationCertificate.getClass() == ElementaryFile.class &*&
	    nonRepudiationCertificate |-> ?theNonRepudiationCertificate &*& theNonRepudiationCertificate.ElementaryFile(_, _, _, _, _, _) &*& theNonRepudiationCertificate.getClass() == ElementaryFile.class &*&
	    preferencesFile |-> ?thePreferencesFile &*& thePreferencesFile != theCaCertificate &*& thePreferencesFile != theRrnCertificate &*& thePreferencesFile.ElementaryFile(_, _, ?thePreferencesFileData, _, _, _) &*& thePreferencesFile != null &*& thePreferencesFileData != null &*& thePreferencesFileData.length == 100 &*& thePreferencesFile.getClass() == ElementaryFile.class &*&
	    belpicSibs == cons<File>(theTokenInfo, cons(theObjectDirectoryFile, cons(theAuthenticationObjectDirectoryFile, cons(thePrivateKeyDirectoryFile, cons(theCertificateDirectoryFile, cons(theCaCertificate, cons(theRrnCertificate, cons(theRootCaCertificate, cons(theAuthenticationCertificate, cons(theNonRepudiationCertificate, nil)))))))))) &*&
	    idSibs == cons<File>(theIdentityFile, cons(theIdentityFileSignature, cons(theAddressFile, cons(theAddressFileSignature, cons(thecaRoleIDFile, cons(thePreferencesFile, cons(thePhotoFile, nil))))))) &*&
	    selected_file_types(theSelectedFile, theMasterFile, theBelpicDirectory, theIdDirectory, theIdentityFile, theIdentityFileSignature, theAddressFile, theAddressFileSignature, thePhotoFile, thecaRoleIDFile, theDirFile, theTokenInfo, theObjectDirectoryFile, theAuthenticationObjectDirectoryFile, thePrivateKeyDirectoryFile, theCaCertificate, theCertificateDirectoryFile, theRrnCertificate, theRootCaCertificate, theAuthenticationCertificate, theNonRepudiationCertificate, thePreferencesFile, _) &*&
    	    (theSelectedFile.getClass() == ElementaryFile.class || theSelectedFile.getClass() == MasterFile.class || theSelectedFile.getClass() == DedicatedFile.class) &*&
	    signatureAlgorithm |-> ?theSignatureAlgorithm &*&
	    nonRepKeyPair |-> ?theNonRepKeyPair &*& theNonRepKeyPair != null &*&
	    authKeyPair |-> ?theAuthKeyPair &*& theAuthKeyPair != null &*&
	    basicKeyPair |-> ?theBasicKeyPair &*&
	    PKCS1_HEADER |-> ?thePKCS1HEADER &*&
	    //EidCard_PKCS1_HEADER(?thePKCS1HEADER) &*&
	     thePKCS1HEADER != null &*& array_slice(thePKCS1HEADER, 0, thePKCS1HEADER.length, _) &*& thePKCS1HEADER.length == 1 &*&
	    PKCS1_SHA1_HEADER |-> ?thePKCS1SHA1HEADER &*& thePKCS1SHA1HEADER != null &*& array_slice(thePKCS1SHA1HEADER, 0, thePKCS1SHA1HEADER.length, _) &*& thePKCS1SHA1HEADER.length == 16 &*&
	    PKCS1_MD5_HEADER |-> ?thePKCS1MD5HEADER &*& thePKCS1MD5HEADER != null &*& array_slice(thePKCS1MD5HEADER, 0, thePKCS1MD5HEADER.length, _) &*& thePKCS1MD5HEADER.length == 19 &*&
	    theDirFile != thePreferencesFile &*& theTokenInfo != thePreferencesFile &*& thePreferencesFile != theObjectDirectoryFile &*& thePreferencesFile != theAuthenticationObjectDirectoryFile &*& thePreferencesFile != thePrivateKeyDirectoryFile
	    ;
    	@*/

	/* APDU header related constants */
	// codes of CLA byte in the command APDUs
	private final static byte EIDCARD_CLA_2 = (byte) 0x80;
	private final static byte EIDCARD_CLA_1 = (byte) 0x00;
	// codes of INS byte in the command APDUs
	private final static byte INS_GET_RESPONSE = (byte) 0xC0;
	private final static byte INS_SELECT_FILE = (byte) 0xA4;
	private final static byte INS_ACTIVATE_FILE = (byte) 0x44;
	private final static byte INS_DEACTIVATE_FILE = (byte) 0x04;
	private final static byte INS_READ_BINARY = (byte) 0xB0;
	private final static byte INS_UPDATE_BINARY = (byte) 0xD6;
	private final static byte INS_ERASE_BINARY = (byte) 0x0E;
	private final static byte INS_VERIFY_PIN = (byte) 0x20;
	private final static byte INS_CHANGE_PIN = (byte) 0x24;
	private final static byte INS_UNBLOCK = (byte) 0x2C;
	private final static byte INS_GET_CHALLENGE = (byte) 0x84;
	private final static byte INS_INTERNAL_AUTHENTICATE = (byte) 0x88;

	private final static byte INS_EXTERNAL_AUTHENTICATE = (byte) 0x82;

	private final static byte INS_ENVELOPE = (byte) 0xC2;
	private final static byte INS_PREPARE_SIGNATURE = (byte) 0x22;
	private final static byte INS_GENERATE_SIGNATURE = (byte) 0x2A;
	private final static byte INS_GENERATE_KEYPAIR = (byte) 0x46;
	private final static byte INS_GET_KEY = (byte) 0xE2;
	private final static byte INS_PUT_KEY = (byte) 0xF2;
	private final static byte INS_ERASE_KEY = (byte) 0xF4;
	private final static byte INS_ACTIVATE_KEY = (byte) 0xF6;
	private final static byte INS_DEACTIVATE_KEY = (byte) 0xF8;
	private final static byte INS_GET_CARD_DATA = (byte) 0xE4;
	private final static byte INS_LOG_OFF = (byte) 0xE6;
	private final static byte INS_BLOCK = (byte) 0xE8;
	private byte[] previousApduType; // transient byte array with 1 element
	// "generate signature" needs to know whether the previous APDU checked the
	// cardholder PIN
	private final static byte VERIFY_CARDHOLDER_PIN = (byte) 0x01;
	// PIN Change needs to know whether the previous APDU checked the reset PIN
	private final static byte VERIFY_RESET_PIN = (byte) 0x02;
	private final static byte GENERATE_KEY_PAIR = (byte) 0x03;
	private final static byte OTHER = (byte) 0x00;
	/* applet specific status words */
	// some are defined in ISO7816, but not by JavaCard

	private final static short SW_CANCELLED = (short) 0xFFFF;
	private final static short SW_ALGORITHM_NOT_SUPPORTED = (short) 0x9484;
	// last nibble of SW2 needs to be overwritten by the counter value/number of
	// PIN tries left
	private final static short SW_WRONG_PIN_0_TRIES_LEFT = (short) 0x63C0;
	private final static short SW_INCONSISTENT_P1P2 = (short) 0x6A87;
	private final static short SW_REFERENCE_DATA_NOT_FOUND = (short) 0x6A88;
	// wrong Le field; SW2 encodes the exact number of available data bytes
	private final static short SW_WRONG_LENGTH_00 = (short) 0x6C00;
	/* PIN related variables */
	// offsets within PIN related APDUs
	private final static byte OFFSET_PIN_HEADER = ISO7816.OFFSET_CDATA;
	private final static byte OFFSET_PIN_DATA = ISO7816.OFFSET_CDATA + 1;
	
	private final static byte OFFSET_SECOND_PIN_HEADER = ISO7816.OFFSET_CDATA + 8;

	private final static byte OFFSET_SECOND_PIN_DATA = ISO7816.OFFSET_CDATA + 9;

	private final static byte OFFSET_SECOND_PIN_DATA_END = ISO7816.OFFSET_CDATA + 15;
	// 4 different PIN codes
	protected final static byte PIN_SIZE = 8;
	protected final static byte CARDHOLDER_PIN = (byte) 0x01;
	protected final static byte CARDHOLDER_PIN_TRY_LIMIT = 3;
	protected final static byte RESET_PIN = (byte) 0x02;
	protected final static byte RESET_PIN_TRY_LIMIT = 10;
	protected final static byte UNBLOCK_PIN = (byte) 0x03;
	protected final static byte UNBLOCK_PIN_TRY_LIMIT = 12;
	protected final static byte ACTIVATE_PIN = (byte) 0x84;
	protected final static byte ACTIVATE_PIN_TRY_LIMIT = 15;
	protected OwnerPIN cardholderPin;
	protected OwnerPIN resetPin;
	protected OwnerPIN unblockPin;
	protected OwnerPIN activationPin;
	//protected OwnerPIN cardholderPin, resetPin, unblockPin, activationPin;
	
	
	/* signature related variables */
	private byte signatureAlgorithm;
	private final static byte ALG_PKCS1 = (byte) 0x01;
	private final static byte ALG_SHA1_PKCS1 = (byte) 0x02;
	private final static byte ALG_MD5_PKCS1 = (byte) 0x04;
	private final static byte[] PKCS1_HEADER = { (byte) 0x00 };
	private final static byte[] PKCS1_SHA1_HEADER = { 0x00, (byte) 0x30, (byte) 0x21, (byte) 0x30, (byte) 0x09, (byte) 0x06, (byte) 0x05, (byte) 0x2b, (byte) 0x0e, (byte) 0x03, (byte) 0x02, (byte) 0x1a, (byte) 0x05, (byte) 0x00, (byte) 0x04,
			(byte) 0x14 };
	private final static byte[] PKCS1_MD5_HEADER = { (byte) 0x00, (byte) 0x30, (byte) 0x20, (byte) 0x30, (byte) 0x0c, (byte) 0x06, (byte) 0x08, (byte) 0x2a, (byte) 0x86, (byte) 0x48, (byte) 0x86, (byte) 0xf7, (byte) 0x0d, (byte) 0x02, (byte) 0x05,
			(byte) 0x05, (byte) 0x00, (byte) 0x04, (byte) 0x10 };
	private byte[] signatureType; // transient byte array with 1 element
	private final static byte NO_SIGNATURE = (byte) 0x00;
	private final static byte BASIC = (byte) 0x81;
	private final static byte AUTHENTICATION = (byte) 0x82;
	private final static byte NON_REPUDIATION = (byte) 0x83;
	private final static byte CA_ROLE = (byte) 0x87;
	
	// make this static to save some memory
	protected static KeyPair basicKeyPair;
	protected static KeyPair authKeyPair;
	protected static KeyPair nonRepKeyPair;
	
	
	
	// reuse these objects in all subclasses, otherwise we will use up all
	// memory
	private static Cipher cipher;
	private static RandomData randomData;
	// this buffer is used to correct PKCS#1 clear text message
	private static byte[] messageBuffer;
	/*
	 * "file system" related variables see Belgian Electronic Identity Card
	 * content
	 */
	protected final static short MF = (short) 0x3F00;
	protected final static short EF_DIR = (short) 0x2F00;
	protected final static short DF_BELPIC = (short) 0xDF00;
	protected final static short DF_ID = (short) 0xDF01;
	protected MasterFile masterFile;
	protected DedicatedFile belpicDirectory, idDirectory;
	protected ElementaryFile dirFile;
	// data under BELPIC directory
	protected final static short ODF = (short) 0x5031;
	protected final static short TOKENINFO = (short) 0x5032;
	protected final static short AODF = (short) 0x5034;
	protected final static short PRKDF = (short) 0x5035;
	protected final static short CDF = (short) 0x5037;
	protected final static short AUTH_CERTIFICATE = (short) 0x5038;
	protected final static short NONREP_CERTIFICATE = (short) 0x5039;
	protected final static short CA_CERTIFICATE = (short) 0x503A;
	protected final static short ROOT_CA_CERTIFICATE = (short) 0x503B;
	protected final static short RRN_CERTIFICATE = (short) 0x503C;
	protected ElementaryFile objectDirectoryFile, tokenInfo, authenticationObjectDirectoryFile, privateKeyDirectoryFile, certificateDirectoryFile, authenticationCertificate, nonRepudiationCertificate, caCertificate, rootCaCertificate, rrnCertificate;
	// data under ID directory
	protected final static short IDENTITY = (short) 0x4031;
	protected final static short SGN_IDENTITY = (short) 0x4032;
	protected final static short ADDRESS = (short) 0x4033;
	protected final static short SGN_ADDRESS = (short) 0x4034;
	protected final static short PHOTO = (short) 0x4035;
	protected final static short CA_ROLE_ID = (short) 0x4038;
	protected final static short PREFERENCES = (short) 0x4039;
	protected ElementaryFile identityFile, identityFileSignature, addressFile, addressFileSignature, photoFile, caRoleIDFile, preferencesFile;

	/*
	 * different file operations see ISO 7816-4 table 17+18
	 */
	// access mode byte for EFs
	private final static byte READ_BINARY = (byte) 0x01;

	private final static byte SEARCH_BINARY = (byte) 0x01;
	private final static byte UPDATE_BINARY = (byte) 0x02;
	private final static byte ERASE_BINARY = (byte) 0x02;

	private final static byte WRITE_BINARY = (byte) 0x04;
	// access mode byte for DFs

	private final static byte DELETE_CHILD_FILE = (byte) 0x01;

	private final static byte CREATE_EF = (byte) 0x02;

	private final static byte CREATE_DF = (byte) 0x04;
	// access mode byte common to DFs and EFs

	private final static byte DEACTIVATE_FILE = (byte) 0x08;

	private final static byte ACTIVATE_FILE = (byte) 0x10;

	private final static byte TERMINATE_FILE = (byte) 0x20;

	private final static byte DELETE_FILE = (byte) 0x40;
	/* variables to pass information between different APDU commands */
	// last generated random challenge will be stored in this buffer
	private byte[] randomBuffer;
	// last generated response (e.g. signature) will be stored in this buffer
	private byte[] responseBuffer;
	// file selected by SELECT FILE; defaults to the MF
	private File selectedFile;
	// only 5000 internal authenticates can be done and then the activation
	// PIN needs to be checked again
	private short internalAuthenticateCounter = 5000;
	/**
	 * called by the JCRE to create an applet instance
	 */
	public static void install(byte[] bArray, short bOffset, byte bLength) 
  	    //@ requires class_init_token(EidCard.class) &*& system();
      	    //@ ensures true;
	{
		// create a eID card applet instance
		new EidCard();
	}
	
	/**
	 * Initialise all files on the card as empty with max size
	 * 
	 * see "Belgian Electronic Identity Card content" (version x)
	 * 
	 * depending on the eid card version, the address is of different length
	 * (current: 117)
	 */
	private void initializeFileSystem() 
  	    /*@ requires identityFile |-> _ &*& identityFileSignature |-> _ &*& addressFile |-> _ &*& addressFileSignature |-> _
			  &*& caRoleIDFile |-> _ &*& preferencesFile |-> _ &*& idDirectory |-> _
			  &*& certificateDirectoryFile |-> _ &*& privateKeyDirectoryFile |-> _ &*& authenticationObjectDirectoryFile |-> _ &*& objectDirectoryFile |-> _
			  &*& tokenInfo |-> _ &*& belpicDirectory |-> _ &*& dirFile |-> _
			  &*& masterFile |-> _ &*& selectedFile |-> _;
	    @*/
      	/*@ ensures dirFile |-> ?theDirFile &*& theDirFile.ElementaryFile(_, _, ?dirFileData, _, _, _) &*& theDirFile != null 
      	              &*& dirFileData != null &*& dirFileData.length == 0x25
	         &*& belpicDirectory |-> ?theBelpicDirectory &*& theBelpicDirectory.DedicatedFile(_, _, _, ?belpic_siblings, _) &*& theBelpicDirectory != null
	         &*& tokenInfo |-> ?theTokenInfo &*& theTokenInfo.ElementaryFile(_, _, ?tokenInfoData, _, _, _) &*& theTokenInfo != null
	              &*& tokenInfoData != null &*& tokenInfoData.length == 0x30
	         &*& objectDirectoryFile |-> ?theObjectDirectoryFile &*& theObjectDirectoryFile.ElementaryFile(_, _, ?objectDirectoryFileData, _, _, _) &*& theObjectDirectoryFile != null
	              &*& objectDirectoryFileData != null &*& objectDirectoryFileData.length == 40
	         &*& authenticationObjectDirectoryFile |-> ?theAuthenticationObjectDirectoryFile &*& theAuthenticationObjectDirectoryFile.ElementaryFile(_, _, ?authenticationObjectDirectoryFileData, _, _, _) &*& theAuthenticationObjectDirectoryFile != null
	              &*& authenticationObjectDirectoryFileData != null &*& authenticationObjectDirectoryFileData.length == 0x40
	         &*& privateKeyDirectoryFile |-> ?thePrivateKeyDirectoryFile &*& thePrivateKeyDirectoryFile.ElementaryFile(_, _, ?privateKeyDirectoryFileData, _, _, _) &*& thePrivateKeyDirectoryFile != null
	              &*& privateKeyDirectoryFileData != null &*& privateKeyDirectoryFileData.length == 0xB0
	         &*& certificateDirectoryFile |-> ?theCertificateDirectoryFile &*& theCertificateDirectoryFile.ElementaryFile(_, _, ?certificateDirectoryFileData, _, _, _) &*& theCertificateDirectoryFile !=  null
	              &*& certificateDirectoryFileData != null &*& certificateDirectoryFileData.length == 0xB0
	         &*& idDirectory |-> ?theIdDirectory &*& theIdDirectory.DedicatedFile(_, _, _, ?idDirectory_siblings, _) &*& theIdDirectory != null
	         &*& identityFile |-> ?theIdentityFile &*& theIdentityFile.ElementaryFile(_, _, ?identityData, _, _, _) &*& theIdentityFile != null
	              &*& identityData != null &*& identityData.length == 0xD0
	         &*& identityFileSignature |-> ?theIdentityFileSignature &*& theIdentityFileSignature.ElementaryFile(_, _, ?identitySignatureData, _, _, _) &*& theIdentityFileSignature != null
	              &*& identitySignatureData != null &*& identitySignatureData.length == 0x80
	         &*& addressFile |-> ?theAddressFile &*& theAddressFile.ElementaryFile(_, _, ?addressFileData, _, _, _) &*& theAddressFile != null
	              &*& addressFileData != null &*& addressFileData.length == 117
	         &*& addressFileSignature |-> ?theAddressFileSignature &*& theAddressFileSignature.ElementaryFile(_, _, ?addressFileSignatureData, _, _, _) &*& theAddressFileSignature != null
	              &*& addressFileSignatureData != null &*& addressFileSignatureData.length == 128
	         &*& caRoleIDFile |-> ?theCaRoleIDFile &*& theCaRoleIDFile.ElementaryFile(_, _, ?caRoldIDFileData, _, _, _) &*& theCaRoleIDFile != null
	              &*& caRoldIDFileData != null &*& caRoldIDFileData.length == 0x20
	         &*& preferencesFile |-> ?thePreferencesFile &*& thePreferencesFile.ElementaryFile(_, _, ?preferencesFileData, _, _, _) &*& thePreferencesFile != null
	              &*& preferencesFileData != null &*& preferencesFileData.length == 100
	         &*& masterFile |-> ?theMasterFile &*& theMasterFile.MasterFile(0x3F00, null, _, ?master_siblings, _) &*& theMasterFile != null
	         &*& master_siblings == cons<File>(theDirFile, cons(theBelpicDirectory, cons(theIdDirectory, nil)))
	         &*& belpic_siblings == cons<File>(theTokenInfo, cons(theObjectDirectoryFile, cons(theAuthenticationObjectDirectoryFile, cons(thePrivateKeyDirectoryFile, cons(theCertificateDirectoryFile,nil)))))
	         &*& idDirectory_siblings == cons<File>(theIdentityFile, cons(theIdentityFileSignature, cons(theAddressFile, cons(theAddressFileSignature, cons(theCaRoleIDFile, cons(thePreferencesFile, nil))))))
	         &*& selectedFile |-> theMasterFile &*& theBelpicDirectory.getClass() == DedicatedFile.class &*& theIdDirectory.getClass() == DedicatedFile.class;
	    @*/
	{
		masterFile = new MasterFile();
		/*
		 * initialize PKCS#15 data structures see
		 * "5. PKCS#15 information details" for more info
		 */
		
		//@ masterFile.castMasterToDedicated();
		
		dirFile = new ElementaryFile(EF_DIR, masterFile, (short) 0x25);
		belpicDirectory = new DedicatedFile(DF_BELPIC, masterFile);
		tokenInfo = new ElementaryFile(TOKENINFO, belpicDirectory, (short) 0x30);
		objectDirectoryFile = new ElementaryFile(ODF, belpicDirectory, (short) 40);
		authenticationObjectDirectoryFile = new ElementaryFile(AODF, belpicDirectory, (short) 0x40);
		privateKeyDirectoryFile = new ElementaryFile(PRKDF, belpicDirectory, (short) 0xB0);
		certificateDirectoryFile = new ElementaryFile(CDF, belpicDirectory, (short) 0xB0);
		idDirectory = new DedicatedFile(DF_ID, masterFile);
		/*
		 * initialize all citizen data stored on the eID card copied from sample
		 * eID card 000-0000861-85
		 */
		// initialize ID#RN EF
		identityFile = new ElementaryFile(IDENTITY, idDirectory, (short) 0xD0);
		// initialize SGN#RN EF
		identityFileSignature = new ElementaryFile(SGN_IDENTITY, idDirectory, (short) 0x80);
		// initialize ID#Address EF
		// address is 117 bytes, and should be padded with zeros
		addressFile = new ElementaryFile(ADDRESS, idDirectory, (short) 117);
		// initialize SGN#Address EF
		addressFileSignature = new ElementaryFile(SGN_ADDRESS, idDirectory, (short) 128);
		// initialize PuK#7 ID (CA Role ID) EF
		caRoleIDFile = new ElementaryFile(CA_ROLE_ID, idDirectory, (short) 0x20);
		// initialize Preferences EF to 100 zero bytes
		preferencesFile = new ElementaryFile(PREFERENCES, idDirectory, (short) 100);
		
		selectedFile = masterFile;
		//@ masterFile.castDedicatedToMaster();
	}
	
	/**
	 * erase data in file that was selected with SELECT FILE
	 */
	private void eraseBinary(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// check if access to this file is allowed
		if (!fileAccessAllowed(ERASE_BINARY))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		// use P1 and P2 as offset
		short offset = Util.makeShort(buffer[ISO7816.OFFSET_P1], buffer[ISO7816.OFFSET_P2]);
		JCSystem.beginTransaction();
		//@ open valid(); // hard to eliminate as the conjunct selectedFile.ElementaryFile depends on non-input parameters
		if (selectedFile == masterFile)
			ISOException.throwIt(ISO7816.SW_FILE_INVALID); //~allow_dead_code Dead because fileAccessAllowed() checks that selectedFile instanceof ElementaryFile and masterFile is not an ElementaryFile.
		// impossible to start erasing from offset large than size of file
		//@ open selected_file_types(_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _);
		short size = ((ElementaryFile)selectedFile).getCurrentSize();
		
		if (offset > size || offset < 0)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		((ElementaryFile) selectedFile).eraseData(offset);
		////@ close valid(); // auto
		JCSystem.commitTransaction();
	}
	/**
	 * change data in a file that was selected with SELECT FILE
	 */
	private void updateBinary(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// check if access to this file is allowed
		if (!fileAccessAllowed(UPDATE_BINARY))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		// use P1 and P2 as offset
		short offset = Util.makeShort(buffer[ISO7816.OFFSET_P1], buffer[ISO7816.OFFSET_P2]);
		// impossible to start updating from offset larger than max size of file
		// this however does not imply that the file length can not change
		JCSystem.beginTransaction();
		//@ open valid();
		if (selectedFile == masterFile)
			ISOException.throwIt(ISO7816.SW_FILE_INVALID); //~allow_dead_code Dead because fileAccessAllowed() checks that selectedFile instanceof ElementaryFile and masterFile is not an ElementaryFile.
		//@ open selected_file_types(_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _);
		short size = ((ElementaryFile) selectedFile).getMaxSize();
		if (offset > size)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		// number of bytes in file starting from offset
		// short remaining = (short) (size - offset);
		// get the new data
		short byteRead = apdu.setIncomingAndReceive();
		// check Lc
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc == 0) || (byteRead == 0))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		// update file
		if (offset < 0 || ISO7816.OFFSET_CDATA + lc > buffer.length || offset + lc > size)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		((ElementaryFile) selectedFile).updateData(offset, buffer, ISO7816.OFFSET_CDATA, lc);
		// //@ close valid(); // auto
		JCSystem.commitTransaction();
	}
	/**
	 * checks if a certain file operation is allowed on the currently selected
	 * file
	 * 
	 * remark 1: a very dedicated (so not generic) implementation! a more
	 * elegant solution would be to put (parts of) access control in File
	 * objects
	 * 
	 * remark 2: there is a huge hack to allow some write updates. this hack is
	 * harmless, as these write operations happen during the copying of a card,
	 * not during its use
	 */
	private boolean fileAccessAllowed(byte mode) 
  	    //@ requires [?f]selectedFile |-> ?theSelectedFile &*& [f]this.preferencesFile |-> ?thePreferencesFile &*& [f]this.cardholderPin |-> ?theCardHolderPin &*& theCardHolderPin != null &*& [f]OwnerPIN(theCardHolderPin, _, _);
      	    //@ ensures [f]selectedFile |-> theSelectedFile &*& [f]this.preferencesFile |-> thePreferencesFile &*& [f]this.cardholderPin |-> theCardHolderPin &*& [f]OwnerPIN(theCardHolderPin, _, _) &*& theSelectedFile instanceof ElementaryFile;
	{
			// if selected file is not an EF, throw "no current EF" exception
		if (!(selectedFile instanceof ElementaryFile))
			ISOException.throwIt(ISO7816.SW_COMMAND_NOT_ALLOWED);
		// always allow READ BINARY
		if (mode == READ_BINARY) {
				return true;
		}
		// allow write access to the preference file if the cardholder pin was
		// entered correctly
		if ((selectedFile == preferencesFile) && cardholderPin.isValidated()) {
				return true;
		}
		// we abuse the activation pin to update some of the large files (photo
		// + certificates)
		if (GPSystem.getCardContentState() == GPSystem.APPLICATION_SELECTABLE) {
				return true;			
		}
			// default to false
		return false;
	}
	/**
	 * Gives back information on this eID
	 * 
	 * @param apdu
	 * @param buffer
	 */
	private void getCardData(APDU apdu, byte[] buffer) 
  	    //@ requires [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// check P1 and P2
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00 || buffer[ISO7816.OFFSET_P2] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		// inform the JCRE that the applet has data to return
		apdu.setOutgoing();
		
		////@ open [1/2]valid();
								
		byte[] data = identityFile.getData(); 
		// Only the chip number is of importance: get this at tag position 2
		short pos = 1;
		//@ open [1/2]identityFile.ElementaryFile(_, _, ?identityFileData, _, _, ?info); // todo (integrate with array_element search)
		short dataLen = (short) data[pos];
		pos = (short) (pos + 1 + dataLen + 1);
		////@ close [1/2]identityFile.ElementaryFile(_, _, identityFileData, _, _, info); // auto
		if (dataLen <= 0 || dataLen + pos + 2 >= identityFile.getCurrentSize())
			ISOException.throwIt(ISO7816.SW_DATA_INVALID);
		//@ open [1/2]identityFile.ElementaryFile(_, _, identityFileData, _, _, info);
		dataLen = (short) data[pos];
		pos = (short) (pos + 1);
		////@ close [1/2]identityFile.ElementaryFile(_, _, identityFileData, _, _, info); // auto
		if (dataLen < 0 || pos + dataLen >= identityFile.getCurrentSize())
			ISOException.throwIt(ISO7816.SW_DATA_INVALID);
		//@ open [1/2]identityFile.ElementaryFile(_, _, identityFileData, _, _, info);
		// check Le
		// if (le != dataLen)
		// ISOException.throwIt((short)(ISO7816.SW_WRONG_LENGTH));
		/*VF*byte version[] = { (byte) 0xA5, (byte) 0x03, (byte) 0x01, (byte) 0x01, (byte) 0x01, (byte) 0x11, (byte) 0x00, (byte) 0x02, (byte) 0x00, (byte) 0x01, (byte) 0x01, (byte) 0x0F };*/
		byte version[] = new byte[] { (byte) 0xA5, (byte) 0x03, (byte) 0x01, (byte) 0x01, (byte) 0x01, (byte) 0x11, (byte) 0x00, (byte) 0x02, (byte) 0x00, (byte) 0x01, (byte) 0x01, (byte) 0x0F };
		byte chipNumber[] = new byte[(short) (dataLen + 12)];
		Util.arrayCopy(data, pos, chipNumber, (short) 0, dataLen);
		Util.arrayCopy(version, (short) 0, chipNumber, dataLen, (short) 12);
		// //Set serial number
		// Util.arrayCopy(tokenInfo.getData(), (short) 7, tempBuffer, (short) 0,
		// (short) 16);
		//		
		// //Set component code: TODO
		//		
		//		
		// //Set OS number: TODO
		//		
		//		
		// //Set OS version: TODO
		// JCSystem.getVersion();
		//		
		// //Set softmask number: TODO
		//		
		// //Set softmask version: TODO
		//		
		// //Set applet version: TODO : 4 bytes in file system
		//		
		//		
		// //Set Interface version: TODO
		//		
		// //Set PKCS#15 version: TODO
		//		
		// //Set applet life cycle
		// tempBuffer[(short)(le-1)] = GPSystem.getCardState();
		// set the actual number of outgoing data bytes
		apdu.setOutgoingLength((short) chipNumber.length);
		// send content of buffer in apdu
		apdu.sendBytesLong(chipNumber, (short) 0, (short) chipNumber.length);
								
		////@ close [1/2]identityFile.ElementaryFile(_, _, identityFileData, _, _, info); // auto
		////@ close [1/2]valid(); // auto
	}
	
	/**
	 * put file that was selected with SELECT FILE in a response APDU
	 */
	private void readBinary(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		////@ open [1/2]valid(); // auto
		// check if access to this file is allowed
		if (!fileAccessAllowed(READ_BINARY))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		// use P1 and P2 as offset
		short offset = Util.makeShort(buffer[ISO7816.OFFSET_P1], buffer[ISO7816.OFFSET_P2]);
		if (offset < 0)
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		// inform the JCRE that the applet has data to return
		short le = apdu.setOutgoing();
		// impossible to start reading from offset large than size of file				
		if (selectedFile == masterFile)
			ISOException.throwIt(ISO7816.SW_FILE_INVALID); //~allow_dead_code Dead because fileAccessAllowed() checks that selectedFile instanceof ElementaryFile and masterFile is not an ElementaryFile.
		//@ open selected_file_types(_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _);
		short size = ((ElementaryFile) selectedFile).getCurrentSize();
		if (offset > size)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		// number of bytes in file starting from offset
		short remaining = (short) (size - offset);
		if (le == 0) {
			if (remaining < 256) {
				// wrong Le field
				// SW2 encodes the exact number of available data bytes
				short sw = (short) (ISO7816.SW_CORRECT_LENGTH_00 | remaining);
				ISOException.throwIt(sw);
			} else
				// Le = 0 is interpreted as 256 bytes
				le = 256;
		}
		// only read out the remaining bytes
		if (le > remaining) {
			le = remaining;
		}
		// set the actual number of outgoing data bytes
		apdu.setOutgoingLength(le);
		// write selected file in APDU
		//VF bug; was   apdu.sendBytesLong(((ElementaryFile) selectedFile).getData(), offset, le);
		//VF probleem: originele lijn was    apdu.sendBytesLong(ef.getData(), offset, le);
		// het probleem hiermee is dat de getData()-methode een ElementaryFile nodig heeft, en dat
		// sendBytesLong vereist dat het resultaat niet null is. De niet-null vereiste zit geencodeerd
		// in ElementaryFile, dus als je dat predicaat opent, dan weet VF dat de data niet-null is, maar
		// dan werkt de call op getData niet. Als je de ElementaryFile gesloten laat, dan lukt de call naar
		// getData, maar weet je niet dat het niet-null is.
		ElementaryFile ef = (ElementaryFile)selectedFile;
		byte[] bf = ef.getData();
		//@ open [1/2]ef.ElementaryFile(?d1, ?d2, ?d3, ?d4, ?d5, ?info); // hard to eliminate
		apdu.sendBytesLong(bf, offset, le);
		////@ close [1/2]ef.ElementaryFile(d1, d2, d3, d4, d5, info); // auto
		////@ close [1/2]valid(); // auto
	}
	
	/**
	 * activate a file on the eID card security conditions depend on file to
	 * activate: see belgian eID content file
	 */
	private void activateFile(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// check P2
		if (buffer[ISO7816.OFFSET_P2] != (byte) 0x0C)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		// P1 determines the select method
		switch (buffer[ISO7816.OFFSET_P1]) {
		case (byte) 0x02:
			selectByFileIdentifier(apdu, buffer);
			break;
		case (byte) 0x08:
			selectByPath(apdu, buffer);
			break;
		default:
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
			break; //~allow_dead_code
		}
		// check if activating this file is allowed
		if (!fileAccessAllowed(UPDATE_BINARY))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		JCSystem.beginTransaction();
		//@ open valid(); // hard to eliminate
		//@ open selected_file_types(_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ?sf2);
		//@ sf2.castElementaryToFile();
		selectedFile.setActive(true);
		//@ sf2.castFileToElementary();
		////@ close valid(); // auto
		JCSystem.commitTransaction();
	}	
	
	/*VF* COPIED FROM EmptyEidCard */
	static byte[] dirData;
	static byte[] tokenInfoData;
	static byte[] odfData;
	static byte[] aodfData;
	static byte[] prkdfData;
	static byte[] cdfData;
	static byte[] citizenCaCert;
	static byte[] rrnCert;
	static byte[] rootCaCert;
	static byte[] photoData;  // save some more memory by making the photo static as well
	
	/**
	 * perform any cleanup tasks and set default selectedFile
	 */
	private void clear() 
    	    //@ requires current_applet(this) &*& [1/2]valid();
      	    //@ ensures current_applet(this) &*& [1/2]valid();
	{
		JCSystem.beginTransaction();
		
		// //@ open valid(); // auto

		// clear signature and random data buffer
		Util.arrayFillNonAtomic(randomBuffer, (short) 0, (short) 256, (byte) 0);
		Util.arrayFillNonAtomic(responseBuffer, (short) 0, (short) 128, (byte) 0);
		// no EF and DF selected yet; select MF by default
		selectedFile = masterFile;
		// invalidate cardholder PIN
		cardholderPin.reset();
		/*
		 * clear text message buffer, signature and previous ADPU type are
		 * transient so no need to reset these manually
		 */

		// open selectedFile.File(?d1, ?d2);
		////@ close valid(); // auto

		JCSystem.commitTransaction();
	}
	/**
	 * initialize empty files that need to be filled latter using UPDATE BINARY
	 */
	private void initializeEmptyLargeFiles() 
	    /*@ requires belpicDirectory |-> ?bpd &*& bpd != null &*& bpd.DedicatedFile(_, _, _, ?belpic_sibs, _) &*& 
	     		length(belpic_sibs) < 6 &*&
	    		idDirectory |-> ?idd &*& idd != null &*& idd.DedicatedFile(_, _, _, ?iddir_sibs, _) &*& 
	    		length(iddir_sibs) < 7 &*&
	    		caCertificate |-> _ &*& rrnCertificate |-> _ &*& rootCaCertificate |-> _ &*& 
	    		photoFile |-> _ &*& authenticationCertificate |-> _ &*& nonRepudiationCertificate |-> _; @*/
      	    /*@ ensures belpicDirectory |-> bpd &*& 
	    		idDirectory |-> idd &*&
	    		caCertificate |-> ?cac &*& cac.ElementaryFile(CA_CERTIFICATE, bpd, ?d1, true, 0, _) &*& d1 != null &*& d1.length == 1200 &*&
	    		rrnCertificate |-> ?rrnc &*&  rrnc.ElementaryFile(RRN_CERTIFICATE, bpd, ?d2, true, 0, _) &*& d2 != null &*& d2.length == 1200 &*&
	    		rootCaCertificate |-> ?rootcac &*&  rootcac.ElementaryFile(ROOT_CA_CERTIFICATE, bpd, ?d3, true, 0, _) &*& d3 != null &*& d3.length == 1200 &*&
	    		photoFile |-> ?pf &*&  pf.ElementaryFile(PHOTO, idd, ?d4, true, 0, _) &*& d4 != null &*& d4.length == 3584 &*&
	    		authenticationCertificate |-> ?ac &*&  ac.ElementaryFile(AUTH_CERTIFICATE, bpd, ?d5, true, 0, _) &*& d5 != null &*& d5.length == 1200 &*&
	    		nonRepudiationCertificate |-> ?nrc &*&  nrc.ElementaryFile(NONREP_CERTIFICATE, bpd, ?d6, true, 0, _) &*& d6 != null &*& d6.length == 1200 &*&
	    		idd.DedicatedFile(_, _, _, append(iddir_sibs, cons(pf, nil)), _) &*& 
	    		bpd.DedicatedFile(_, _, _, append(append(append(append(append(belpic_sibs, cons(cac, nil)), cons(rrnc, nil)), cons(rootcac, nil)), cons(ac, nil)), cons(nrc, nil)), _); @*/
	{
		/*
		 * these 3 certificates are the same for all sample eid card applets
		 * therefor they are made static and the data is allocated only once
		 */
		caCertificate = new ElementaryFile(CA_CERTIFICATE, belpicDirectory, (short) 1200);
		rrnCertificate = new ElementaryFile(RRN_CERTIFICATE, belpicDirectory, (short) 1200);
		
		rootCaCertificate = new ElementaryFile(ROOT_CA_CERTIFICATE, belpicDirectory, (short) 1200);
		/*
		 * to save some memory we only support 1 photo for all subclasses
		 * ideally this should be applet specific and have max size 3584 (3.5K)
		 */
		photoFile = new ElementaryFile(PHOTO, idDirectory, (short) 3584);
		/*
		 * certificate #2 and #3 are applet specific allocate enough memory
		 */
		authenticationCertificate = new ElementaryFile(AUTH_CERTIFICATE, belpicDirectory, (short) 1200);
		nonRepudiationCertificate = new ElementaryFile(NONREP_CERTIFICATE, belpicDirectory, (short) 1200);
	}
	
	/**
	 * initialize basic key pair
	 */
	private void initializeKeyPairs() 
  	    //@ requires nonRepKeyPair |-> _ &*& authKeyPair |-> _ &*& basicKeyPair |-> _;
      	    /*@ ensures nonRepKeyPair |-> ?theNonRepKeyPair &*& theNonRepKeyPair != null &*&
	      	    authKeyPair |-> ?theAuthKeyPair &*& theAuthKeyPair != null &*&
	      	    basicKeyPair |-> ?theBasicKeyPair &*& theBasicKeyPair != null;
	    @*/
	{
		/*
		 * basicKeyPair is static (so same for all applets) so only allocate
		 * memory once
		 */
		if (EidCard.basicKeyPair != null && authKeyPair != null && nonRepKeyPair != null) {
			return;
		}
		
		
		basicKeyPair = new KeyPair(KeyPair.ALG_RSA_CRT, (short) 1024);
		basicKeyPair.genKeyPair();
		
		authKeyPair = new KeyPair(KeyPair.ALG_RSA_CRT, (short) (1024));
		authKeyPair.genKeyPair();
		
		
	
		//authPrivateKey = (RSAPrivateCrtKey) KeyBuilder.buildKey(KeyBuilder.TYPE_RSA_CRT_PRIVATE, KeyBuilder.LENGTH_RSA_1024, false);
		

		nonRepKeyPair = new KeyPair(KeyPair.ALG_RSA_CRT, (short) (1024));
		nonRepKeyPair.genKeyPair();
	
		//nonRepPrivateKey = (RSAPrivateCrtKey) KeyBuilder.buildKey(KeyBuilder.TYPE_RSA_CRT_PRIVATE, KeyBuilder.LENGTH_RSA_1024, false);
	}
	/**
	 * select file under the current DF
	 */
	private void selectByFileIdentifier(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// receive the data to see which file needs to be selected
		short byteRead = apdu.setIncomingAndReceive();
		// check Lc
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc != 2) || (byteRead != 2))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		// get the file identifier out of the APDU
		short fid = Util.makeShort(buffer[ISO7816.OFFSET_CDATA], buffer[ISO7816.OFFSET_CDATA + 1]);
		JCSystem.beginTransaction();
		//@ open valid(); // todo (implement patterns as arguments to rules instead of terms )
		//@ assert selected_file_types(_, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, _);
		// if file identifier is the master file, select it immediately
		if (fid == MF)
			selectedFile = masterFile;		
		else {
			// check if the requested file exists under the current DF
			////@ close masterFile.DedicatedFile();
			////@ MasterFile theMasterFile = masterFile; // auto
			////@ assert theMasterFile.MasterFile(16128, null, ?x1, ?x2, ?x3); // auto
			////@ close theMasterFile.DedicatedFile(16128, null, x1, x2, x3); // auto
			File s = ((DedicatedFile) masterFile).getSibling(fid);
			////@ open theMasterFile.DedicatedFile(16128, null, x1, x2, x3); // auto
			//VF /bug
			if (s != null) {
				selectedFile = s;
			//the fid is an elementary file:
			} else {
				s = belpicDirectory.getSibling(fid);
				if (s != null) {
					selectedFile = s;
				} else {
					s = idDirectory.getSibling(fid);
					if (s != null) {
						selectedFile = s;
						
					} else {
						ISOException.throwIt(ISO7816.SW_FILE_NOT_FOUND);
					}
				}
				
			}
			//@ close selected_file_types(s, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, _);	
		}	
		
		// //@ close valid(); // auto
		JCSystem.commitTransaction();
	}
	/**
	 * select file by path from the MF
	 */
	private void selectByPath(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// receive the path name
		short byteRead = apdu.setIncomingAndReceive();
		// check Lc
		////@ masking_and(buffer[ISO7816.OFFSET_LC], 0x00FF);
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		// it must be a multiple of 2
		if (((lc & 1) == 1) || ((byteRead & 1) == 1))
			ISOException.throwIt(SW_INCONSISTENT_P1P2);
		if (buffer.length < ISO7816.OFFSET_CDATA + lc + 1)
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		////@ open [1/2]valid(); // auto
		// use the path name in the APDU data to select a file
		File f = masterFile;
		////@ assert [1/2]masterFile |-> ?theMasterFile;
		for (byte i = 0; i < lc; i += 2) 
		    /*@ invariant array_slice(buffer, 0, buffer.length, _) &*& i >= 0 &*& i < (lc + 2) &*& 
		    			[1/2]randomBuffer |-> ?theRandomBuffer &*& theRandomBuffer != null &*& [1/2]array_slice(theRandomBuffer, 0, theRandomBuffer.length, _) &*& theRandomBuffer.length == 256 &*&
				    [1/2]responseBuffer |-> ?theResponseBuffer &*& theResponseBuffer != null &*& [1/2]array_slice(theResponseBuffer, 0, theResponseBuffer.length, _) &*& theResponseBuffer.length == 128 &*&
				    [1/2]randomData |-> ?theRandomData &*& theRandomData != null &*&
				    [1/2]cipher |-> ?theCipher &*& theCipher != null &*&
				    [1/2]messageBuffer |-> ?theMessageBuffer &*& theMessageBuffer != null &*& theMessageBuffer.length == 128 &*& is_transient_byte_array(theMessageBuffer) == true &*&
				    [1/2]previousApduType |-> ?thePreviousApduType &*& thePreviousApduType != null &*& thePreviousApduType.length == 1 &*& is_transient_byte_array(thePreviousApduType) == true &*&
				    [1/2]signatureType |-> ?theSignatureType &*& theSignatureType != null &*& theSignatureType.length == 1 &*& is_transient_byte_array(theSignatureType) == true &*&
				    [1/2]masterFile |-> ?theMasterFile &*& [1/2]theMasterFile.MasterFile(0x3F00, null, _, ?masterSibs, _) &*& theMasterFile != null &*& theMasterFile.getClass() == MasterFile.class &*&
				    [1/2]cardholderPin |-> ?theCardholderPin &*& [1/2]OwnerPIN(theCardholderPin, _, _) &*& theCardholderPin != null &*& 
				    [1/2]resetPin |-> ?theResetPin &*& [1/2]OwnerPIN(theResetPin, _, _) &*& theResetPin != null &*&
				    [1/2]unblockPin |-> ?theUnblockPin &*& [1/2]OwnerPIN(theUnblockPin, _, _) &*& theUnblockPin != null &*&
				    [1/2]activationPin |-> ?theActivationPin &*& [1/2]OwnerPIN(theActivationPin, _, _) &*& theActivationPin != null &*&
				    [1/2]identityFile |-> ?theIdentityFile &*& [1/2]theIdentityFile.ElementaryFile(_, _, ?identityData, _, _, _) &*& theIdentityFile != null &*& identityData != null &*& identityData.length == 0xD0 &*& theIdentityFile.getClass() == ElementaryFile.class &*&
				    [1/2]identityFileSignature |-> ?theIdentityFileSignature &*& [1/2]theIdentityFileSignature.ElementaryFile(_, _, ?theIdentityFileSignatureData, _, _, _) &*& theIdentityFileSignature != null &*& theIdentityFileSignatureData != null &*& theIdentityFileSignatureData.length == 0x80 &*& theIdentityFileSignature.getClass() == ElementaryFile.class &*&
				    [1/2]addressFile |-> ?theAddressFile &*& [1/2]theAddressFile.ElementaryFile(_, _, ?theAddressFileData, _, _, _) &*& theAddressFile != null &*& theAddressFileData != null &*& theAddressFileData.length == 117 &*& theAddressFile.getClass() == ElementaryFile.class &*&
				    [1/2]addressFileSignature |-> ?theAddressFileSignature &*& [1/2]theAddressFileSignature.ElementaryFile(_, _, ?theAddressFileSignatureData, _, _, _) &*& theAddressFileSignature != null &*& theAddressFileSignatureData != null &*& theAddressFileSignatureData.length == 128 &*& theAddressFileSignature.getClass() == ElementaryFile.class &*&
				    [1/2]photoFile |-> ?thePhotoFile &*& [1/2]thePhotoFile.ElementaryFile(_, _, _, _, _, _) &*& thePhotoFile != null &*& thePhotoFile.getClass() == ElementaryFile.class &*&
				    [1/2]caRoleIDFile |-> ?thecaRoleIDFile &*& [1/2]thecaRoleIDFile.ElementaryFile(_, _, ?theCaRoleIDFileData, _, _, _) &*& thecaRoleIDFile != null &*& theCaRoleIDFileData != null &*& theCaRoleIDFileData.length == 0x20 &*& thecaRoleIDFile.getClass() == ElementaryFile.class &*&
				    [1/2]dirFile |-> ?theDirFile &*& [1/2]theDirFile.ElementaryFile(_, _, ?theDirFileData, _, _, _) &*& theDirFile != null &*& theDirFileData != null &*& theDirFileData.length ==  0x25 &*& theDirFile.getClass() == ElementaryFile.class &*&
				    [1/2]tokenInfo |-> ?theTokenInfo &*& [1/2]theTokenInfo.ElementaryFile(_, _, ?theTokenInfoData, _, _, _) &*& theTokenInfo != null &*& theTokenInfoData != null &*& theTokenInfoData.length == 0x30 &*& theTokenInfo.getClass() == ElementaryFile.class &*&
				    [1/2]objectDirectoryFile |-> ?theObjectDirectoryFile &*& [1/2]theObjectDirectoryFile.ElementaryFile(_, _, ?theObjectDirectoryFileData, _, _, _) &*& theObjectDirectoryFile != null &*& theObjectDirectoryFileData != null &*& theObjectDirectoryFileData.length == 40 &*& theObjectDirectoryFile.getClass() == ElementaryFile.class &*&
				    [1/2]authenticationObjectDirectoryFile |-> ?theAuthenticationObjectDirectoryFile &*& [1/2]theAuthenticationObjectDirectoryFile.ElementaryFile(_, _, ?theAuthenticationObjectDirectoryFileData, _, _, _) &*& theAuthenticationObjectDirectoryFile != null &*& theAuthenticationObjectDirectoryFileData != null &*& theAuthenticationObjectDirectoryFileData.length == 0x40 &*&  theAuthenticationObjectDirectoryFile.getClass() == ElementaryFile.class &*&
				    [1/2]privateKeyDirectoryFile |-> ?thePrivateKeyDirectoryFile &*& [1/2]thePrivateKeyDirectoryFile.ElementaryFile(_, _, ?thePrivateKeyDirectoryFileData, _, _, _) &*& thePrivateKeyDirectoryFile != null &*& thePrivateKeyDirectoryFileData != null &*& thePrivateKeyDirectoryFileData.length == 0xB0 &*& thePrivateKeyDirectoryFile.getClass() == ElementaryFile.class &*&
				    [1/2]certificateDirectoryFile |-> ?theCertificateDirectoryFile &*& [1/2]theCertificateDirectoryFile.ElementaryFile(_, _, ?theCertificateDirectoryFileData, _, _, _) &*& theCertificateDirectoryFile != null &*& theCertificateDirectoryFileData != null &*& theCertificateDirectoryFileData.length == 0xB0 &*& theCertificateDirectoryFile.getClass() == ElementaryFile.class &*&
				    [1/2]belpicDirectory |-> ?theBelpicDirectory &*& [1/2]theBelpicDirectory.DedicatedFile(_, _, _, ?belpicSibs, _) &*& theBelpicDirectory != null &*& theBelpicDirectory.getClass() == DedicatedFile.class &*&
				    [1/2]idDirectory |-> ?theIdDirectory &*& [1/2]theIdDirectory.DedicatedFile(_, _, _, ?idSibs, _) &*& theIdDirectory != null &*& theIdDirectory.getClass() == DedicatedFile.class &*&
				    [1/2]caCertificate |-> ?theCaCertificate &*& [1/2]theCaCertificate.ElementaryFile(_, _, _, _, _, _) &*& theCaCertificate.getClass() == ElementaryFile.class &*&
				    [1/2]selectedFile |-> ?theSelectedFile &*& theSelectedFile != null &*&
				    masterSibs == cons<File>(theDirFile, cons(theBelpicDirectory, cons(theIdDirectory, nil))) &*&
				    [1/2]rootCaCertificate |-> ?theRootCaCertificate &*& [1/2]theRootCaCertificate.ElementaryFile(_, _, _, _, _, _) &*& theRootCaCertificate.getClass() == ElementaryFile.class &*&
				    [1/2]rrnCertificate |-> ?theRrnCertificate &*& [1/2]theRrnCertificate.ElementaryFile(_, _, _, _, _, _) &*& theRrnCertificate.getClass() == ElementaryFile.class &*&
				    [1/2]authenticationCertificate |-> ?theAuthenticationCertificate &*& [1/2]theAuthenticationCertificate.ElementaryFile(_, _, _, _, _, _) &*& theAuthenticationCertificate.getClass() == ElementaryFile.class &*&
				    [1/2]nonRepudiationCertificate |-> ?theNonRepudiationCertificate &*& [1/2]theNonRepudiationCertificate.ElementaryFile(_, _, _, _, _, _) &*& theNonRepudiationCertificate.getClass() == ElementaryFile.class &*&
				    [1/2]preferencesFile |-> ?thePreferencesFile &*& thePreferencesFile != theCaCertificate &*& thePreferencesFile != theRrnCertificate &*& [1/2]thePreferencesFile.ElementaryFile(_, _, ?thePreferencesFileData, _, _, _) &*& thePreferencesFile != null &*& thePreferencesFileData != null &*& thePreferencesFileData.length == 100 &*& thePreferencesFile.getClass() == ElementaryFile.class &*&
				    belpicSibs == cons<File>(theTokenInfo, cons(theObjectDirectoryFile, cons(theAuthenticationObjectDirectoryFile, cons(thePrivateKeyDirectoryFile, cons(theCertificateDirectoryFile, cons(theCaCertificate, cons(theRrnCertificate, cons(theRootCaCertificate, cons(theAuthenticationCertificate, cons(theNonRepudiationCertificate, nil)))))))))) &*&
				    idSibs == cons<File>(theIdentityFile, cons(theIdentityFileSignature, cons(theAddressFile, cons(theAddressFileSignature, cons(thecaRoleIDFile, cons(thePreferencesFile, cons(thePhotoFile, nil))))))) &*&
				    [1/2]selected_file_types(theSelectedFile, theMasterFile, theBelpicDirectory, theIdDirectory, theIdentityFile, theIdentityFileSignature, theAddressFile, theAddressFileSignature, thePhotoFile, thecaRoleIDFile, theDirFile, theTokenInfo, theObjectDirectoryFile, theAuthenticationObjectDirectoryFile, thePrivateKeyDirectoryFile, theCaCertificate, theCertificateDirectoryFile, theRrnCertificate, theRootCaCertificate, theAuthenticationCertificate, theNonRepudiationCertificate, thePreferencesFile, _) &*&
			    	    (theSelectedFile.getClass() == ElementaryFile.class || theSelectedFile.getClass() == MasterFile.class || theSelectedFile.getClass() == DedicatedFile.class) &*&
			      	    /*internalAuthenticateCounter |-> ?theInternalAuthenticateCounter &*&*/
				    [1/2]signatureAlgorithm |-> ?theSignatureAlgorithm &*&
				    [1/2]nonRepKeyPair |-> ?theNonRepKeyPair &*& theNonRepKeyPair != null &*&
				    [1/2]authKeyPair |-> ?theAuthKeyPair &*& theAuthKeyPair != null &*&
				    [1/2]basicKeyPair |-> ?theBasicKeyPair &*&
				    [1/2]PKCS1_HEADER |-> ?thePKCS1HEADER &*& thePKCS1HEADER != null &*& [1/2]array_slice(thePKCS1HEADER, 0, thePKCS1HEADER.length, _) &*& thePKCS1HEADER.length == 1 &*&
				    [1/2]PKCS1_SHA1_HEADER |-> ?thePKCS1SHA1HEADER &*& thePKCS1SHA1HEADER != null &*& [1/2]array_slice(thePKCS1SHA1HEADER, 0, thePKCS1SHA1HEADER.length, _) &*& thePKCS1SHA1HEADER.length == 16 &*&
				    [1/2]PKCS1_MD5_HEADER |-> ?thePKCS1MD5HEADER &*& thePKCS1MD5HEADER != null &*& [1/2]array_slice(thePKCS1MD5HEADER, 0, thePKCS1MD5HEADER.length, _) &*& thePKCS1MD5HEADER.length == 19 &*&
				    theDirFile != thePreferencesFile &*& theTokenInfo != thePreferencesFile &*& thePreferencesFile != theObjectDirectoryFile &*& thePreferencesFile != theAuthenticationObjectDirectoryFile &*& thePreferencesFile != thePrivateKeyDirectoryFile &*&
				    (f == null ? 
				      true 
				        : 
				      selected_file_types(f, theMasterFile, theBelpicDirectory, theIdDirectory, theIdentityFile, theIdentityFileSignature, theAddressFile, theAddressFileSignature, thePhotoFile, thecaRoleIDFile, theDirFile, theTokenInfo, theObjectDirectoryFile, theAuthenticationObjectDirectoryFile, thePrivateKeyDirectoryFile, theCaCertificate, theCertificateDirectoryFile, theRrnCertificate, theRootCaCertificate, theAuthenticationCertificate, theNonRepudiationCertificate, thePreferencesFile, _) &*&
				      f.getClass() == ElementaryFile.class || f.getClass() == MasterFile.class || f.getClass() == DedicatedFile.class			                 
				    ) &*&
				    (i == 0 ? 
				      f == theMasterFile 
				        :
				      (i <= 2 ?
				        f == null || f == theMasterFile || mem(f, masterSibs) 
				          :
				        (i <= 4 ?
				          f == null || mem(f, masterSibs) || mem(f, belpicSibs) || mem(f, idSibs)
				        :
				          (i <= 6 ?
				            f == null || mem(f, belpicSibs) || mem(f, idSibs)
				              :
				            false
				          )
				        )
				      )
				    ); @*/
		{
			short fid = Util.makeShort(buffer[(short) (ISO7816.OFFSET_CDATA + i)], buffer[(short) (ISO7816.OFFSET_CDATA + i + 1)]);
			// MF can be explicitely or implicitely in the path name
			if ((i == 0) && (fid == MF))
				f = masterFile;
			else {
			        
				if ((f instanceof ElementaryFile) || f == null)
					ISOException.throwIt(ISO7816.SW_FILE_NOT_FOUND);
				//@ open selected_file_types(f, theMasterFile, theBelpicDirectory, theIdDirectory, theIdentityFile, theIdentityFileSignature, theAddressFile, theAddressFileSignature, thePhotoFile, thecaRoleIDFile, theDirFile, theTokenInfo, theObjectDirectoryFile, theAuthenticationObjectDirectoryFile, thePrivateKeyDirectoryFile, theCaCertificate, theCertificateDirectoryFile, theRrnCertificate, theRootCaCertificate, theAuthenticationCertificate, theNonRepudiationCertificate, thePreferencesFile, _);
				//@ File oldf = f;
				/*@ 
				if(f == masterFile) 
				{} else if (f == idDirectory) {} else {}
				@*/
				/*@
				if(f == masterFile) {
				  masterFile.castMasterToDedicated();
		  		}	  		
		  		@*/
				f = ((DedicatedFile) f).getSibling(fid);
				/*@ if(oldf == masterFile) {
			  	      masterFile.castDedicatedToMaster();
			  	      assert f == null || (f == idDirectory && f.getClass() == DedicatedFile.class) || (f == belpicDirectory && f.getClass() == DedicatedFile.class)|| (f == dirFile && f.getClass() == ElementaryFile.class);
				    } 
				@*/
				/*@
				  if(f != null) {
				    close selected_file_types(f, theMasterFile, theBelpicDirectory, theIdDirectory, theIdentityFile, theIdentityFileSignature, theAddressFile, theAddressFileSignature, thePhotoFile, thecaRoleIDFile, theDirFile, theTokenInfo, theObjectDirectoryFile, theAuthenticationObjectDirectoryFile, thePrivateKeyDirectoryFile, theCaCertificate, theCertificateDirectoryFile, theRrnCertificate, theRootCaCertificate, theAuthenticationCertificate, theNonRepudiationCertificate, thePreferencesFile, _);
				  }
				@*/
				
			}
		}
		if (f == null)
			ISOException.throwIt(ISO7816.SW_FILE_NOT_FOUND);

		JCSystem.beginTransaction();
		////@ open [1/2]valid(); // auto
		////@ open selected_file_types(f, ?g1, ?g2, ?g3, ?g4, ?g5, ?g6, ?g7, ?g8, ?g9, ?g10, ?g11, ?g12, ?g13, ?g14, ?g15, ?g16, ?g17, ?g18, ?g19, ?g20, ?g21, _);
		selectedFile = f;
		////@ close selected_file_types(f, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, _);
		////@ close valid(); // auto
		JCSystem.commitTransaction();
	}

	/*VF* END COPY */
	

	/**
	 * initialize all the PINs
	 * 
	 * PINs are set to the same values as the sample eID card
	 */
	private void initializePins() 
  	    /*@ requires this.cardholderPin |-> _ &*& this.resetPin |-> _
  	    			&*& this.unblockPin |-> _ &*& this.activationPin |-> _;
  	    @*/
      	    /*@ ensures this.cardholderPin |-> ?theCardholderPin &*& OwnerPIN(theCardholderPin, _, _) &*& theCardholderPin != null 
			&*& this.resetPin |-> ?theResetPin &*& OwnerPIN(theResetPin, _, _) &*& theResetPin != null
			&*& this.unblockPin |-> ?theUnblockPin &*& OwnerPIN(theUnblockPin, _, _) &*& theUnblockPin != null
			&*& this.activationPin |-> ?theActivationPin &*& OwnerPIN(theActivationPin, _, _) &*& theActivationPin != null;
      	    @*/
      	    //this.cardholderPin |-> ?theCardholderPin &*& 
	{
		/*
		 * initialize cardholder PIN (hardcoded to fixed value)
		 * 
		 * PIN header is "24" (length of PIN = 4) PIN itself is "1234" (4
		 * digits) fill rest of PIN data with F
		 */
		/*VF*byte[] cardhold = { (byte) 0x24, (byte) 0x12, (byte) 0x34, (byte) 0xFF, (byte) 0xFF, (byte) 0xFF, (byte) 0xFF, (byte) 0xFF }; */
		byte cardhold[] = new byte[] { (byte) 0x24, (byte) 0x12, (byte) 0x34, (byte) 0xFF, (byte) 0xFF, (byte) 0xFF, (byte) 0xFF, (byte) 0xFF };
		cardholderPin = new OwnerPIN(CARDHOLDER_PIN_TRY_LIMIT, PIN_SIZE);
		cardholderPin.update(cardhold, (short) 0, PIN_SIZE);
		/*
		 * initialize unblock PUK (hardcoded to fixed value)
		 * 
		 * PUK header is "2c" (length of PUK = 12) PUK itself consists of 2
		 * parts PUK2 is "222222" (6 digits) PUK1 is "111111" (6 digits) so in
		 * total the PUK is "222222111111" (12 digits) fill last bye of PUK data
		 * with "FF"
		 */
		/*VF* byte[] unblock = { (byte) 0x2c, (byte) 0x22, (byte) 0x22, (byte) 0x22, (byte) 0x11, (byte) 0x11, (byte) 0x11, (byte) 0xFF }; */
		byte unblock[] = new byte[] { (byte) 0x2c, (byte) 0x22, (byte) 0x22, (byte) 0x22, (byte) 0x11, (byte) 0x11, (byte) 0x11, (byte) 0xFF };
		unblockPin = new OwnerPIN(UNBLOCK_PIN_TRY_LIMIT, PIN_SIZE);
		unblockPin.update(unblock, (short) 0, PIN_SIZE);
		/*
		 * activation PIN is same as PUK
		 */
		activationPin = new OwnerPIN(ACTIVATE_PIN_TRY_LIMIT, PIN_SIZE);
		activationPin.update(unblock, (short) 0, PIN_SIZE);
		/*
		 * initialize reset PIN (hardcoded to fixed value)
		 * 
		 * PUK header is "2c" (length of PUK = 12) PIN itself consists of 2
		 * parts PUK3 is "333333" (6 digits) PUK1 is "111111" (6 digits) so in
		 * total the PIN is "333333111111" (12 digits) fill last bye of PIN data
		 * with "FF"
		 */
		/*VF* byte[] reset = { (byte) 0x2c, (byte) 0x33, (byte) 0x33, (byte) 0x33, (byte) 0x11, (byte) 0x11, (byte) 0x11, (byte) 0xFF }; */
		byte reset[] = new byte[] { (byte) 0x2c, (byte) 0x33, (byte) 0x33, (byte) 0x33, (byte) 0x11, (byte) 0x11, (byte) 0x11, (byte) 0xFF };
		resetPin = new OwnerPIN(RESET_PIN_TRY_LIMIT, PIN_SIZE);
		resetPin.update(reset, (short) 0, PIN_SIZE);
	}
	
	/**
	 * private constructor - called by the install method to instantiate a
	 * EidCard instance
	 * 
	 * needs to be protected so that it can be invoked by subclasses
	 */
	protected EidCard() 
    	/*@ requires class_init_token(EidCard.class) &*& system(); @*/
    	//@ ensures true;
	{
		//@ init_class();
		//internalAuthenticateCounter = 5000;

		randomBuffer = new byte[256];
		responseBuffer = new byte[128];
		// initialize these objects once for the superclass
		// otherwise we have RAM problems when running multiple EidCard applets
		if (EidCard.randomData == null)
			EidCard.randomData = RandomData.getInstance(RandomData.ALG_SECURE_RANDOM);
		if (EidCard.cipher == null)
			EidCard.cipher = Cipher.getInstance(Cipher.ALG_RSA_NOPAD, false);
		Cipher c =  Cipher.getInstance(Cipher.ALG_RSA_NOPAD, false);
		if (EidCard.messageBuffer == null)
			EidCard.messageBuffer = JCSystem.makeTransientByteArray((short) 128, JCSystem.CLEAR_ON_DESELECT);
		// make these transient objects so that they are stored in RAM
		previousApduType = JCSystem.makeTransientByteArray((short) 1, JCSystem.CLEAR_ON_DESELECT);
		signatureType = JCSystem.makeTransientByteArray((short) 1, JCSystem.CLEAR_ON_DESELECT);
		// register the applet instance with the JCRE

		/*VF* COPIED FROM EmptyEidCard */
		// initialize PINs to fixed value
		initializePins();
		// initialize file system
		initializeFileSystem();
		// initialize place holders for large files (certificates + photo)
		initializeEmptyLargeFiles();
		// initialize basic keys pair
		initializeKeyPairs();
		/*VF* END COPY */
 		//@ preferencesFile.neq(caCertificate);
 		//@ preferencesFile.neq(rrnCertificate);
 		//@ preferencesFile.neq(dirFile);
 		//@ preferencesFile.neq(tokenInfo);
 		//@ preferencesFile.neq(objectDirectoryFile);
 		//@ preferencesFile.neq(authenticationObjectDirectoryFile);
 		//@ preferencesFile.neq(privateKeyDirectoryFile);
		////@ close valid(); // auto
		register();
	}
	/**
	 * initialize the applet when it is selected
	 * 
	 * select always has to happen after a reset
	 */
	public boolean select() 
            //@ requires current_applet(this) &*& [1/2]valid();
            //@ ensures current_applet(this) &*& [1/2]valid();
	{
		// Clear data and set default selectedFile to masterFile
		clear();
		return true;
	}
	/**
	 * perform any cleanup and bookkeeping tasks before the applet is deselected
	 */
	public void deselect() 
    	    //@ requires current_applet(this) &*& [1/2]valid();
    	    //@ ensures current_applet(this) &*& [1/2]valid();
	{
		clear();
		return;
	}
	/**
	 * process APDUs
	 */
	public void process(APDU apdu) 
            //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, ?buffer_) &*& array_slice(buffer_, 0, buffer_.length, _);
            //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer_) &*& array_slice(buffer_, 0, buffer_.length, _);
	{
		byte[] buffer = apdu.getBuffer();
		/*
		 * - non repudiation signatures can only be generated if the previous
		 * APDU verified the cardholder PIN - administrator PIN change is only
		 * possible if the previous APDU verified the reset PIN
		 * 
		 * so only the "generate signature" and PIN Change APDU needs to check
		 * the previous APDU type; in all other cases overwrite the previous
		 * APDU type, because this information is not needed; we do this as
		 * early as possible to cope with exceptions being thrown during
		 * processing of APDU
		 * 
		 * IMPORTANT : we have to set the previous APDU type in the processing
		 * of a PIN Verify APDU (because the type gets overwritten to a wrong
		 * value) and at the end of a "generate signature" and PIN Change APDU
		 */
		JCSystem.beginTransaction();
		////@ open valid(); // auto
		if ((buffer[ISO7816.OFFSET_INS] != INS_GENERATE_SIGNATURE) && (buffer[ISO7816.OFFSET_INS] != INS_CHANGE_PIN) && (buffer[ISO7816.OFFSET_INS] != INS_GET_KEY))
			setPreviousApduType(OTHER);
		////@ close valid(); // auto
		JCSystem.commitTransaction();
		// return if the APDU is the applet SELECT command
		if (selectingApplet()) {
			return;
		}
		if (buffer[ISO7816.OFFSET_CLA] == EIDCARD_CLA_1)
			// check the INS byte to decide which service method to call
			switch (buffer[ISO7816.OFFSET_INS]) {
			// case INS_CHANGE_ATR :
			// changeATR(apdu);
			// break;
			case INS_VERIFY_PIN:
				verifyPin(apdu, buffer);
				break;
			case INS_CHANGE_PIN:
				changePin(apdu, buffer);
				break;
			case INS_UNBLOCK:
				unblock(apdu, buffer);
				break;
			case INS_GET_CHALLENGE:
				getChallenge(apdu, buffer);
				break;
			case INS_PREPARE_SIGNATURE:
				prepareForSignature(apdu, buffer);
				break;
			case INS_GENERATE_SIGNATURE:
				generateSignature(apdu, buffer);
				break;
			case INS_GENERATE_KEYPAIR:
				generateKeyPair(apdu);
				break;
			case INS_INTERNAL_AUTHENTICATE:
				internalAuthenticate(apdu, buffer);
				break;
			case INS_GET_RESPONSE:
				// if only T=0 supported: remove
				// not possible in case of T=0 protocol
				if (APDU.getProtocol() == APDU.PROTOCOL_T1)
					getResponse(apdu, buffer);
				else
					ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
				break;
			case INS_SELECT_FILE:
				selectFile(apdu, buffer);
				break;
			case INS_ACTIVATE_FILE:
				activateFile(apdu, buffer);
				break;
			case INS_DEACTIVATE_FILE:
				deactivateFile(apdu, buffer);
				break;
			case INS_READ_BINARY:
				readBinary(apdu, buffer);
				break;
			case INS_UPDATE_BINARY:
				updateBinary(apdu, buffer);
				break;
			case INS_ERASE_BINARY:
				eraseBinary(apdu, buffer);
				break;
			default:
				ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
				break; //~allow_dead_code
			}
		else if (buffer[ISO7816.OFFSET_CLA] == EIDCARD_CLA_2)
			switch (buffer[ISO7816.OFFSET_INS]) {
			case INS_GET_KEY:
				getPublicKey(apdu);
				break;
			case INS_PUT_KEY:
				putPublicKey(apdu, buffer);
				break;
			case INS_ERASE_KEY:
				eraseKey(apdu, buffer);
				break;
			case INS_ACTIVATE_KEY:
				activateKey(apdu, buffer);
				break;
			case INS_DEACTIVATE_KEY:
				deactivateKey(apdu, buffer);
				break;
			case INS_GET_CARD_DATA:
				getCardData(apdu, buffer);
				break;
			case INS_LOG_OFF:
				logOff(apdu, buffer);
				break;
			// case INS_BLOCK :
			// blockCard(apdu, buffer);
			// break;
			}
		else
			ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
	}
	/**
	 * verify the PIN
	 */
	private void verifyPin(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		
		// check P1
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		// receive the PIN data for validation
		apdu.setIncomingAndReceive();
		// check PIN depending on value of P2
		JCSystem.beginTransaction();
		////@ open valid(); // auto
		switch (buffer[ISO7816.OFFSET_P2]) {
		case CARDHOLDER_PIN:
			// overwrite previous APDU type
			setPreviousApduType(VERIFY_CARDHOLDER_PIN);
			// check the cardholder PIN
			checkPin(cardholderPin, buffer);
			break;
		case ACTIVATE_PIN:
			// check the activation PIN
			checkPin(activationPin, buffer);
			// if the activation PIN was entered correctly
			if (GPSystem.getCardContentState() == GPSystem.APPLICATION_SELECTABLE)
				// set the applet status to personalized
				GPSystem.setCardContentState(GPSystem.CARD_SECURED);
			// reset internal authenticate counter
			//internalAuthenticateCounter = 5000;
			break;
		case RESET_PIN:
			// overwrite previous APDU type
			setPreviousApduType(VERIFY_RESET_PIN);
			// check the reset PIN
			checkPin(resetPin, buffer);
			break;
		case UNBLOCK_PIN:
			// check the unblock PIN: after this, the pin will be 'activated'
			checkPin(unblockPin, buffer);
			break;
		default:
			ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
		}
		////@ close valid(); // auto
		JCSystem.commitTransaction();
	}
	/**
	 * check the PIN
	 */
	private void checkPin(OwnerPIN pin, byte[] buffer) 
  	    //@ requires [1/2]cardholderPin |-> ?theCardholderPin &*& [1/2]OwnerPIN(pin, _, _) &*& pin != null &*& buffer != null &*& array_slice(buffer, 0, buffer.length, _) &*& buffer.length >= 13;
      	    //@ ensures [1/2]cardholderPin |-> theCardholderPin &*& [1/2]OwnerPIN(pin, _, _) &*& pin != null &*& array_slice(buffer, 0, buffer.length, _) &*& buffer != null &*& buffer.length >= 13;
	{
		if (pin.check(buffer, OFFSET_PIN_HEADER, PIN_SIZE) == true)
			return;
		short tries = pin.getTriesRemaining();
		// the eID card throws this exception, SW=0x63C0 would make more sense
		if (tries == 0) {
			// if the cardholder PIN is no longer valid (too many tries)
			if (pin == cardholderPin)
				// set the applet status to blocked
				GPSystem.setCardContentState(GPSystem.CARD_LOCKED);
			ISOException.throwIt(ISO7816.SW_FILE_INVALID);
		}
		/*
		 * create the correct exception the status word is of the form 0x63Cx
		 * with x the number of tries left
		 */
		short sw = (short) (SW_WRONG_PIN_0_TRIES_LEFT | tries);
		ISOException.throwIt(sw);
	}
	/**
	 * change the PIN
	 */
	private void changePin(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		/*
		 * IMPORTANT: in all other APDUs the previous APDU type gets overwritten
		 * in process() function; this is not the case here because the
		 * information is needed when processing to verify the security
		 * condition for administrator PIN change
		 * 
		 * the previous APDU type has to be overwritten in every possible exit
		 * path out of this function
		 */
		JCSystem.beginTransaction();
		////@ open valid(); // auto
		// check P2
		if (buffer[ISO7816.OFFSET_P2] != (byte) 0x01) {
			setPreviousApduType(OTHER);
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		}
		// P1 determines whether it is user or administrator PIN change
		switch (buffer[ISO7816.OFFSET_P1]) {
		case (byte) 0x00:
			setPreviousApduType(OTHER);
			////@ close valid(); // auto
			JCSystem.commitTransaction();
			userChangePin(apdu, buffer);
			break;
		case (byte) 0x01:
			// //@ close valid(); // auto
			JCSystem.commitTransaction();
			administratorChangePin(apdu, buffer);
			break;
		default:
			setPreviousApduType(OTHER);
			// //@ close valid(); // auto
			JCSystem.commitTransaction();
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
			break; //~allow_dead_code
		}
		
	}
	/**
	 * user changes the PIN
	 */
	private void userChangePin(APDU apdu, byte[] buffer) 
  	    //@ requires [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _) &*& buffer.length > OFFSET_SECOND_PIN_HEADER + PIN_SIZE;
      	    //@ ensures [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _) &*& buffer.length > OFFSET_SECOND_PIN_HEADER + PIN_SIZE;
	{
		////@ open [1/2]valid(); // auto
		// receive the PIN data
		short byteRead = apdu.setIncomingAndReceive();
		// check Lc
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc != 16) || (byteRead != 16))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		// first check old cardholder PIN
		checkPin(cardholderPin, buffer);
		// do some checks on the new PIN header and data
		if (!isNewPinFormattedCorrectly(buffer, OFFSET_SECOND_PIN_HEADER))
			ISOException.throwIt(ISO7816.SW_WRONG_DATA);
		// include header as well in PIN object
		cardholderPin.update(buffer, OFFSET_SECOND_PIN_HEADER, PIN_SIZE);
		// validate cardholder PIN immediately after change PIN
		// so that cardholder access rights are immediately granted
		cardholderPin.check(buffer, OFFSET_SECOND_PIN_HEADER, PIN_SIZE);
		////@ close [1/2]valid(); // auto
	}
	/**
	 * administrator changes the PIN
	 */
	private void administratorChangePin(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// The previous getChallenge() should ask for at least the length of the
		// new administrator pin. Otherwise exception is thrown
		/*
		 * IMPORTANT: the previous APDU type has to be overwritten in every
		 * possible exit path out of this function; therefore we check the
		 * security conditions as early as possible
		 */
		JCSystem.beginTransaction();
		////@ open valid(); // auto
		// previous APDU must have checked the reset PIN
		if ((!resetPin.isValidated()) || (getPreviousApduType() != VERIFY_RESET_PIN)) {
			setPreviousApduType(OTHER);
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		}
		// overwrite previous ADPU type as soon as possible
		setPreviousApduType(OTHER);
		// receive the PIN data
		short byteRead = apdu.setIncomingAndReceive();
		// check Lc
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc != 8) || (byteRead != 8))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		// do some checks on the new PIN header and data
		if (!isNewPinFormattedCorrectly(buffer, OFFSET_PIN_HEADER))
			ISOException.throwIt(ISO7816.SW_WRONG_DATA);
		// compare the new PIN with the last generated random challenge
		if (!isNewPinCorrectValue(buffer))
			ISOException.throwIt(ISO7816.SW_WRONG_DATA);
		// include header as well in PIN object
		cardholderPin.update(buffer, OFFSET_PIN_HEADER, PIN_SIZE);
		////@ close valid(); // auto
		JCSystem.commitTransaction();
	}
	/**
	 * check if new PIN conforms to internal format
	 * 
	 * returns false if new PIN is not formatted correctly
	 */
	private boolean isNewPinFormattedCorrectly(byte[] buffer, byte offset) 
  	    //@ requires buffer != null &*& array_slice(buffer, 0, buffer.length, _) &*& offset >= 0 &*& offset < buffer.length - PIN_SIZE &*& offset + PIN_SIZE <= Byte.MAX_VALUE;
      	    //@ ensures array_slice(buffer, 0, buffer.length, _);
	{
		// 1st nibble of new PIN header should be 2
		if ((buffer[offset] >> 4) != 2)
			return false;
		// 2nd nibble of new PIN header is the length (in digits)
		//@ and_limits(buffer[offset], 0x0F, nat_of_pos(p1(p1(p1_))));
		byte pinLength = (byte) (buffer[offset] & 0x0F);
		// the new PIN should be between 4 and 12 digits
		if (pinLength < 4 || pinLength > 12)
			return false;
		// divide PIN length by 2 to get the length in bytes
		//@ shr_limits(pinLength, 1, nat_of_pos(p1(p1(p1_))));
		byte pinLengthInBytes = (byte) (pinLength >> 1);
		
		// check if PIN length is odd
		if ((pinLength & (byte) 0x01) == (byte) 0x01)
			pinLengthInBytes++;
		// check if PIN data is padded with 0xFF
		byte i = (byte) (offset + PIN_SIZE - 1);
		for (; i > offset + pinLengthInBytes; i--) 
			/*@ invariant array_slice(buffer, 0, buffer.length, _) &*& i >= offset + pinLengthInBytes
				&*& i <= offset + PIN_SIZE - 1;
			@*/
		{
			if (buffer[i] != (byte) 0xFF)
				return false;
		}
		// if PIN length is odd, check if last PIN data nibble is F
		if ((pinLength & (byte) 0x01) == (byte) 0x01) {
			if (/*@truncating@*/ (byte) (buffer[i] << 4) != (byte) 0xF0)
				return false;
		}
		return true;
	}
	/**
	 * check if new PIN is based on the last generated random challenge
	 */
	private boolean isNewPinCorrectValue(byte[] buffer) 
  	    /*@ requires buffer != null &*& array_slice(buffer, 0, buffer.length, _) &*& buffer.length >= OFFSET_PIN_DATA + 8
  	    	  &*& randomBuffer |-> ?theRandomBuffer &*& theRandomBuffer != null &*& array_slice(theRandomBuffer, 0, theRandomBuffer.length, _) &*& theRandomBuffer.length == 256;
  	    @*/
      	    //@ ensures array_slice(buffer, 0, buffer.length, _) &*& randomBuffer |-> theRandomBuffer &*& array_slice(theRandomBuffer, 0, theRandomBuffer.length, _);
	{
		// 2nd nibble of the PIN header is the length (in digits)
		int tmp = buffer[OFFSET_PIN_HEADER];
		if(tmp < 0) { // BUG
		  return false;
		}
		byte pinLength = (byte) (buffer[OFFSET_PIN_HEADER] & 0x0F);
		// check if PIN length is odd
		byte oldLength = (byte) (pinLength & 0x01);
		// divide PIN length by 2 to get the length in bytes
		byte pinLengthInBytes = (byte) (pinLength >> 1);
		//@ assert 0 <= pinLengthInBytes && pinLengthInBytes < 8;
		byte i;
		for (i = 0; i < pinLengthInBytes; i++) 
			/*@ invariant array_slice(buffer, 0, buffer.length, _) &*& i >= 0 &*& i <= pinLengthInBytes 
			       &*& randomBuffer |-> ?theRandomBuffer2 &*& theRandomBuffer == theRandomBuffer2 &*& theRandomBuffer2 != null &*& array_slice(theRandomBuffer2, 0, theRandomBuffer2.length, _) &*& theRandomBuffer2.length >= pinLengthInBytes;
			@*/
		{
			if (buffer[OFFSET_PIN_DATA + i] != (randomBuffer[i] & 0x77))
				return false;
		}
		if (oldLength == (byte) 0x01) {
			if ((buffer[OFFSET_PIN_DATA + pinLengthInBytes] >> 4) != ((randomBuffer[i] & 0x7F) >> 4))
				return false;
		}
		return true;
	}
	/**
	 * Discard current fulfilled access conditions
	 */
	private void logOff(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// check P1 and P2
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00 || buffer[ISO7816.OFFSET_P2] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		// remove previous access conditions:
		JCSystem.beginTransaction();
		////@ open valid(); // auto
		setPreviousApduType(OTHER);
		setSignatureType(NO_SIGNATURE);
		cardholderPin.reset();
		resetPin.reset();
		unblockPin.reset();
		activationPin.reset();
		////@ close valid(); // auto
		JCSystem.commitTransaction();
	}
	/**
	 * unblock card
	 */
	private void unblock(APDU apdu, byte[] buffer) 
  	    //@ requires [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// check P1 and P2
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00 || buffer[ISO7816.OFFSET_P2] != (byte) 0x01)
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		// receive the PUK data for validation
		apdu.setIncomingAndReceive();
		// check PUK
		////@ open valid(); // auto
		checkPin(unblockPin, buffer);
		// if PUK is correct, then unblock cardholder PINs
		cardholderPin.resetAndUnblock();
		// set the applet status back to personalized
		GPSystem.setCardContentState(GPSystem.CARD_SECURED);
		////@ close [1/2]valid(); // auto
	}
	/**
	 * prepare for authentication or non repudiation signature
	 */
	private void prepareForSignature(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// check P1 and P2
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x41 || buffer[ISO7816.OFFSET_P2] != (byte) 0xB6)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		// receive the data to see which kind of signature
		short byteRead = apdu.setIncomingAndReceive();
		// check Lc
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc != 5) || (byteRead != 5))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		// the first 2 bytes of the data part should be 0x04 0x80
		// the fourth byte should be 0x84
		if ((buffer[ISO7816.OFFSET_CDATA] != (byte) 0x04) || (buffer[ISO7816.OFFSET_CDATA + 1] != (byte) 0x80) || (buffer[ISO7816.OFFSET_CDATA + 3] != (byte) 0x84))
			ISOException.throwIt(ISO7816.SW_WRONG_DATA);
		// initialize signature object depending on hash function type
		
		JCSystem.beginTransaction();
		////@ open valid(); // auto
		switch (buffer[ISO7816.OFFSET_CDATA + 2]) {
		case ALG_SHA1_PKCS1:
			signatureAlgorithm = ALG_SHA1_PKCS1;
			break;
		case ALG_MD5_PKCS1:
			signatureAlgorithm = ALG_MD5_PKCS1;
			break;
		case ALG_PKCS1:
			signatureAlgorithm = ALG_PKCS1;
			break;
		default: // algorithm not supported (SW=9484)
			ISOException.throwIt(SW_ALGORITHM_NOT_SUPPORTED);
			break; //~allow_dead_code
		}
		// signature type is determined by the the last byte
		switch (buffer[ISO7816.OFFSET_CDATA + 4]) {
		case BASIC:
			setSignatureType(BASIC);
			break;
		case AUTHENTICATION: // use authentication private key
			setSignatureType(AUTHENTICATION);
			break;
		case NON_REPUDIATION: // use non repudiation private key
			setSignatureType(NON_REPUDIATION);
			break;
		case CA_ROLE:
			setSignatureType(NO_SIGNATURE);
			ISOException.throwIt(ISO7816.SW_WRONG_DATA);
			break; //~allow_dead_code
		default:
			setSignatureType(NO_SIGNATURE);
			ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
			break; //~allow_dead_code
		}
		////@ close valid(); // auto
		JCSystem.commitTransaction();
	}
	/**
	 * generate (authentication or non repudiation) signature
	 */
	private void generateSignature(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		/*
		 * IMPORTANT: in all other APDUs the previous APDU type gets overwritten
		 * in process() function; this is not the case here because the
		 * information is needed when processing to verify the security
		 * condition for non repudiation signature
		 * 
		 * the previous APDU type has to be overwritten in every possible exit
		 * path out of this function; therefore we check the security conditions
		 * of the non repudiation signature as early as possible, but we have to
		 * overwrite the previous APDU type in the 2 possible exceptions before
		 */
		JCSystem.beginTransaction();
		////@ open valid(); // auto
		// check P1 and P2		
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x9E || buffer[ISO7816.OFFSET_P2] != (byte) 0x9A) {
			setPreviousApduType(OTHER);
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		}
		// generate signature without prepare signature results:
		// "conditions of use not satisfied"
		if (getSignatureType() == NO_SIGNATURE) {
			setPreviousApduType(OTHER);
			ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
		}
		/*
		 * verify authentication information throw
		 * "security condition not satisfied" if something is wrong
		 */
		// check if previous APDU did a cardholder PIN verification
		if ((getSignatureType() == NON_REPUDIATION) && (getPreviousApduType() != VERIFY_CARDHOLDER_PIN)) {
			setPreviousApduType(OTHER);
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		}
		// overwrite previous ADPU type as soon as possible
		setPreviousApduType(OTHER);

		// it is impossible to generate basic signatures with this command
		if (getSignatureType() == BASIC)
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		// check if cardholder PIN was entered correctly
		if (!cardholderPin.isValidated())
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		
		////@ close valid(); // auto
		JCSystem.commitTransaction();
		////@ open [1/2]valid(); // auto
		switch (signatureAlgorithm) {
		case ALG_MD5_PKCS1:
			////@ close [1/2]valid(); // auto
			generatePkcs1Md5Signature(apdu, buffer);
			////@ open [1/2]valid(); // auto
			break;
		case ALG_SHA1_PKCS1:
			////@ close [1/2]valid(); // auto
			generatePkcs1Sha1Signature(apdu, buffer);
			////@ open [1/2]valid(); // auto
			break;
		case ALG_PKCS1:
			////@ close [1/2]valid(); // auto
			generatePkcs1Signature(apdu, buffer);
			////@ open [1/2]valid(); // auto
			break;
		}
		////@ close [1/2]valid(); // auto
		// if T=1, store signature in sigBuffer so that it can latter be sent
		if (APDU.getProtocol() == APDU.PROTOCOL_T1) {
			JCSystem.beginTransaction();
			//@ open valid(); // todo (???)
			Util.arrayCopy(buffer, (short) 0, responseBuffer, (short) 0, (short) 128);
			////@ close valid(); // auto
			JCSystem.commitTransaction();
			
			// in case T=0 protocol, send the signature immediately in a
			// response APDU
		} else {
			// send first 128 bytes (= 1024 bit) of buffer
			apdu.setOutgoingAndSend((short) 0, (short) 128);
		}
	}
	/**
	 * generate PKCS#1 MD5 signature
	 */
	private void generatePkcs1Md5Signature(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// receive the data that needs to be signed
		short byteRead = apdu.setIncomingAndReceive();
		// check Lc
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc != 16) || (byteRead != 16))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		// use the correct key
		////@ open [1/2]valid(); // auto
		
		if (getSignatureType() == NON_REPUDIATION) {		
			cipher.init((RSAPrivateCrtKey)nonRepKeyPair.getPrivate(), Cipher.MODE_ENCRYPT);
		}
		if (getSignatureType() == AUTHENTICATION) {
			cipher.init((RSAPrivateCrtKey)authKeyPair.getPrivate(), Cipher.MODE_ENCRYPT);
		}
		////@ close [1/2]valid(); // auto
		JCSystem.beginTransaction();
		
		////@ open valid(); // todo
		
		//@ transient_byte_arrays_mem(messageBuffer);
		//@ assert transient_byte_arrays(?as);
		//@ foreachp_remove(messageBuffer, as);
		////@ open transient_byte_array(messageBuffer); // auto
		
		// prepare the message buffer to the PKCS#1 (v1.5) structure
		////@ open [1/2]valid();
		preparePkcs1ClearText(messageBuffer, ALG_MD5_PKCS1, lc);
		// copy the MD5 hash from the APDU to the message buffer
		Util.arrayCopy(buffer, (short) (ISO7816.OFFSET_CDATA), messageBuffer, (short) (128 - lc), lc);

		//@ close transient_byte_array(messageBuffer);
		//@ foreachp_unremove(messageBuffer, as);

		////@ close valid(); // auto
		JCSystem.commitTransaction();
		////@ open [1/2]valid(); // auto
		// generate signature
		//@ transient_byte_arrays_mem(messageBuffer);
		//@ assert transient_byte_arrays(?as1);
		//@ foreachp_remove(messageBuffer, as1);
		//@ open transient_byte_array(messageBuffer);
		cipher.doFinal(messageBuffer, (short) 0, (short) 128, buffer, (short) 0);
		//@ close transient_byte_array(messageBuffer);
		//@ foreachp_unremove(messageBuffer, as1);

		////@ close [1/2]valid(); // auto


	}
	/**
	 * generate PKCS#1 SHA1 signature
	 */
	private void generatePkcs1Sha1Signature(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// receive the data that needs to be signed
		short byteRead = apdu.setIncomingAndReceive();
		// check Lc
		
		
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc != 20) || (byteRead != 20))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		
		
		////@ open [1/2]valid(); // auto
		// use the correct key
		if (getSignatureType() == NON_REPUDIATION) {
			////cipher.init(nonRepPrivateKey, Cipher.MODE_ENCRYPT); // stond al in comments
			cipher.init((RSAPrivateCrtKey)nonRepKeyPair.getPrivate(), Cipher.MODE_ENCRYPT);
		}
		
		if (getSignatureType() == AUTHENTICATION) {
			cipher.init((RSAPrivateCrtKey)authKeyPair.getPrivate(), Cipher.MODE_ENCRYPT);
		}
		
		////@ close [1/2]valid(); // auto
		JCSystem.beginTransaction();
		////@ open valid(); // auto
		
		//@ transient_byte_arrays_mem(messageBuffer);
		//@ assert transient_byte_arrays(?as);
		//@ foreachp_remove(messageBuffer, as);
		////@ open transient_byte_array(messageBuffer); // auto

		// prepare the message buffer to the PKCS#1 (v1.5) structure
		preparePkcs1ClearText(messageBuffer, ALG_SHA1_PKCS1, lc);
		// copy the SHA1 hash from the APDU to the message buffer
		Util.arrayCopy(buffer, (short) (ISO7816.OFFSET_CDATA), messageBuffer, (short) (128 - lc), lc);

		//@ close transient_byte_array(messageBuffer);
		//@ foreachp_unremove(messageBuffer, as);

		////@ close valid(); // auto
		JCSystem.commitTransaction();
		////@ open [1/2]valid(); // auto
		// generate signature
		//@ transient_byte_arrays_mem(messageBuffer);
		//@ assert transient_byte_arrays(?as1);
		//@ foreachp_remove(messageBuffer, as1);
		////@ open transient_byte_array(messageBuffer); // auto
		cipher.doFinal(messageBuffer, (short) 0, (short) 128, buffer, (short) 0);
		//@ close transient_byte_array(messageBuffer); // todo
		//@ foreachp_unremove(messageBuffer, as1);
		////@ close [1/2]valid(); // auto
	}
	/**
	 * generate PKCS#1 signature
	 */
	private void generatePkcs1Signature(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// receive the data that needs to be signed
		short byteRead = apdu.setIncomingAndReceive();
		// check Lc
		//@ positive_and(buffer[ISO7816.OFFSET_LC], 0x00FF);
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc > 117) || (byteRead > 117))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		// use the correct key
		////@ open [1/2]valid(); // auto
		if (getSignatureType() == NON_REPUDIATION) {
			cipher.init((RSAPrivateCrtKey)nonRepKeyPair.getPrivate(), Cipher.MODE_ENCRYPT);
		}
		if (getSignatureType() == AUTHENTICATION) {
			cipher.init((RSAPrivateCrtKey)authKeyPair.getPrivate(), Cipher.MODE_ENCRYPT);
		}
		////@ close [1/2]valid(); // auto
		JCSystem.beginTransaction();
		////@ open valid(); // auto

		//@ transient_byte_arrays_mem(messageBuffer);
		//@ assert transient_byte_arrays(?as);
		//@ foreachp_remove(messageBuffer, as);
		//@ open transient_byte_array(messageBuffer);

		// prepare the message buffer to the PKCS#1 (v1.5) structure
		preparePkcs1ClearText(messageBuffer, ALG_PKCS1, lc);
		// copy the clear text from the APDU to the message buffer
		Util.arrayCopy(buffer, (short) (ISO7816.OFFSET_CDATA), messageBuffer, (short) (128 - lc), lc);
		//@ close transient_byte_array(messageBuffer);
		//@ foreachp_unremove(messageBuffer, as);

		////@ close valid(); // auto
		JCSystem.commitTransaction();
		////@ open [1/2]valid(); // auto
		//@ transient_byte_arrays_mem(messageBuffer);
		//@ assert transient_byte_arrays(?as1);
		//@ foreachp_remove(messageBuffer, as1);
		////@ open transient_byte_array(messageBuffer); // auto
		// generate signature
		cipher.doFinal(messageBuffer, (short) 0, (short) 128, buffer, (short) 0);
		//@ close transient_byte_array(messageBuffer);
		//@ foreachp_unremove(messageBuffer, as1);
		////@ close [1/2]valid(); // auto
	}
	/**
	 * prepare the clear text buffer with correct PKCS#1 encoding
	 */
	private void preparePkcs1ClearText(byte[] clearText, short type, short messageLength) 
  	    /*@ requires clearText != null &*& array_slice(clearText, 0, clearText.length, _) &*& clearText.length >= 128
	  	    &*& PKCS1_HEADER |-> ?thePKCS1HEADER &*& PKCS1_SHA1_HEADER |-> ?thePKCS1SHA1HEADER &*& PKCS1_MD5_HEADER |-> ?thePKCS1MD5HEADER
	  	    &*& thePKCS1HEADER != null &*& thePKCS1SHA1HEADER != null &*& thePKCS1MD5HEADER != null
	  	    &*& thePKCS1HEADER.length == 1 &*& thePKCS1SHA1HEADER.length == 16 &*& thePKCS1MD5HEADER.length == 19
	  	    &*& array_slice(thePKCS1HEADER, 0, thePKCS1HEADER.length, _)
	  	    &*& array_slice(thePKCS1SHA1HEADER, 0, thePKCS1SHA1HEADER.length, _)
	  	    &*& array_slice(thePKCS1MD5HEADER, 0, thePKCS1MD5HEADER.length, _)
	  	    &*& messageBuffer |-> ?theMessageBuffer &*& theMessageBuffer != null 
	  	    &*& messageLength >= 0
	  	    &*& type == ALG_SHA1_PKCS1 ? messageLength == 20 || messageLength == 22 : type == ALG_MD5_PKCS1 ? messageLength == 16 : messageLength < 126; @*/
      	    /*@ ensures array_slice(clearText, 0, clearText.length, _) &*& PKCS1_HEADER |-> thePKCS1HEADER 
      	    	    &*& PKCS1_SHA1_HEADER |-> thePKCS1SHA1HEADER &*& PKCS1_MD5_HEADER |-> thePKCS1MD5HEADER
	  	    &*& array_slice(thePKCS1HEADER, 0, thePKCS1HEADER.length, _)
	  	    &*& array_slice(thePKCS1SHA1HEADER, 0, thePKCS1SHA1HEADER.length, _)
	  	    &*& array_slice(thePKCS1MD5HEADER, 0, thePKCS1MD5HEADER.length, _)
      	    	    &*& messageBuffer |-> theMessageBuffer ; @*/
	{
		// first pad the whole clear text with 0xFF
		Util.arrayFillNonAtomic(clearText, (short) 0, (short) 128, (byte) 0xff);
		// first 2 bytes should be 0x00 and 0x01
		Util.arrayFillNonAtomic(clearText, (short) 0, (short) 1, (byte) 0x00);
		Util.arrayFillNonAtomic(clearText, (short) 1, (short) 1, (byte) 0x01);
		// add the PKCS#1 header at the correct location
		byte[] header = PKCS1_HEADER;
		if (type == ALG_SHA1_PKCS1)
			header = PKCS1_SHA1_HEADER;
		if (type == ALG_MD5_PKCS1)
			header = PKCS1_MD5_HEADER;
		Util.arrayCopy(header, (short) 0, clearText, (short) (128 - messageLength - header.length), (short) header.length);
	}
	/**
	 * generate a key pair
	 * 
	 * only the private key will be stored in the eid. the get public key method
	 * should be called directly after this method, otherwise the public key
	 * will be discarded security conditions depend on the key to generate the
	 * role R03 (see belgian eid card content) shall be verified for changing
	 * authentication or non repudiation keys.
	 */
	private void generateKeyPair(APDU apdu) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, ?theBuffer) &*& array_slice(theBuffer, 0, theBuffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, theBuffer) &*& array_slice(theBuffer, 0, theBuffer.length, _);
	{
		apdu.setIncomingAndReceive();// If this was removed, function will not
		// work: no data except for command will be read
		byte[] buffer = apdu.getBuffer();
		// check if access to this method is allowed
		if (GPSystem.getCardContentState() != GPSystem.APPLICATION_SELECTABLE)
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		// check P1 and P2
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		// check Lc
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if (lc != (short) 11)
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		byte offset = (ISO7816.OFFSET_CDATA + 0x01);
		//byte offset = (byte)(ISO7816.OFFSET_CDATA + 0x01);
		// create keypair using parameters given:
		// short keyLength = Util.makeShort(buffer[ISO7816.OFFSET_CDATA],
		// buffer[offset]);
		if (buffer[offset] != (byte) 0x80)
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		
		
		
		// This is commented out as changing exponent makes getting modulus
		// impossible on some java cards
		// ((RSAPublicKey)tempkp.getPublic()).setExponent(buffer, (short)(13),
		// (short)3);
		JCSystem.beginTransaction();
		////@ open valid(); // auto
		setPreviousApduType(GENERATE_KEY_PAIR);
		switch (buffer[ISO7816.OFFSET_P2]) {
		case BASIC:
			basicKeyPair = new KeyPair(KeyPair.ALG_RSA_CRT, (short) (1024));
			basicKeyPair.genKeyPair();
			
			break;
		case AUTHENTICATION: // use authentication private key
			authKeyPair = new KeyPair(KeyPair.ALG_RSA_CRT, (short) (1024));
			authKeyPair.genKeyPair();
			
			break;
		case NON_REPUDIATION: // use non repudiation private key
			nonRepKeyPair = new KeyPair(KeyPair.ALG_RSA_CRT, (short) (1024));
			nonRepKeyPair.genKeyPair();
			
			break;
		default:
			
			ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
			break; //~allow_dead_code
		}
		////@ close valid(); // auto
		JCSystem.commitTransaction();
	}
	/**
	 * get a public key. for the authentication and non-repudiation key, this
	 * method can only be called after the generateKeyPair method was called
	 * 
	 */
	private void getPublicKey(APDU apdu) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, ?theBuffer) &*& array_slice(theBuffer, 0, theBuffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, theBuffer) &*& array_slice(theBuffer, 0, theBuffer.length, _);
	{
		
		
		byte[] buffer = apdu.getBuffer();
		// if this is thrown: problem accesses getPreviousapdu
		// check P1
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		// inform the JCRE that the applet has data to return
		short le = apdu.setOutgoing();
		// Le = 0 is not allowed
		if (le != (short) (5 + 8 + 128))
			ISOException.throwIt((short) (SW_WRONG_LENGTH_00 + (5 + 8 + 128)));
		byte[] tempBuffer = new byte[le];
		tempBuffer[(short) 0] = (byte) 0x02;
		tempBuffer[(short) 1] = (byte) 0x08;
		tempBuffer[(short) 10] = (byte) 0x03;
		tempBuffer[(short) 11] = (byte) 0x81;
		tempBuffer[(short) 12] = (byte) 0x80;
		////@ open [1/2]valid(); // auto
		if (buffer[ISO7816.OFFSET_P2] == AUTHENTICATION){
			if (getPreviousApduType() != GENERATE_KEY_PAIR) {
				authKeyPair.getPublic().clearKey();
			        ////@ close [1/2]valid(); // auto
				JCSystem.beginTransaction();
			        ////@ open valid(); // auto
				setPreviousApduType(OTHER);
			        ////@ close valid(); // auto
				JCSystem.commitTransaction();
			        ////@ open [1/2]valid(); // auto
				ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
			}
			((RSAPublicKey) authKeyPair.getPublic()).getExponent(tempBuffer, (short) 7);
			((RSAPublicKey) authKeyPair.getPublic()).getModulus(tempBuffer, (short) 13);
		}else if (buffer[ISO7816.OFFSET_P2] == NON_REPUDIATION) { 
			if (getPreviousApduType() != GENERATE_KEY_PAIR) {
				nonRepKeyPair.getPublic().clearKey();
			        ////@ close [1/2]valid(); // auto
				JCSystem.beginTransaction();
			        ////@ open valid(); // auto
				setPreviousApduType(OTHER);
				////@ close valid(); // auto
				JCSystem.commitTransaction();
				////@ open [1/2]valid(); // auto
				ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
			}			
			((RSAPublicKey) nonRepKeyPair.getPublic()).getExponent(tempBuffer, (short) 7);
			((RSAPublicKey) nonRepKeyPair.getPublic()).getModulus(tempBuffer, (short) 13);
		}else if (buffer[ISO7816.OFFSET_P2] == BASIC) {		
			if (basicKeyPair == null)
				ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
			((RSAPublicKey) basicKeyPair.getPublic()).getExponent(tempBuffer, (short) 7);
			((RSAPublicKey) basicKeyPair.getPublic()).getModulus(tempBuffer, (short) 13);
		} else {
			ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
		}
	        ////@ close [1/2]valid(); // auto
		JCSystem.beginTransaction();
	        ////@ open valid(); // auto
		setPreviousApduType(OTHER);
		////@ close valid(); // auto
		JCSystem.commitTransaction();
		////@ open [1/2]valid(); // auto
		authKeyPair.getPublic().clearKey();
		nonRepKeyPair.getPublic().clearKey();
		// set the actual number of outgoing data bytes
		apdu.setOutgoingLength(le);
		// send content of buffer in apdu
		apdu.sendBytesLong(tempBuffer, (short) 0, le);
		////@ close [1/2]valid(); // auto
	}
	/**
	 * put a public key as commune or role key this is not supported anymore
	 */
	private void putPublicKey(APDU apdu, byte[] buffer) 
  	    //@ requires [1/2]valid();
      	    //@ ensures [1/2]valid();
	{
		ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
	}
	/**
	 * erase a public key (basic, commune or role key) only basic supported
	 */
	private void eraseKey(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// check P1
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		switch (buffer[ISO7816.OFFSET_P2]) {
		case BASIC:
			JCSystem.beginTransaction();
			//@ open valid();
			basicKeyPair = null;
			////@ close valid(); // auto
			JCSystem.commitTransaction();
			break;
		default:
			ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
			break; //~allow_dead_code
		}
	}
	/**
	 * activate a public authentication or non repudiation key if deactivated
	 * keys in this applet are always active
	 */
	private void activateKey(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// check P1
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		switch (buffer[ISO7816.OFFSET_P2]) {
		case AUTHENTICATION:
			// activate key: key always active, do nothing
			break;
		case NON_REPUDIATION:
			// activate key: key always active, do nothing
			break;
		default:
			ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
			break; //~allow_dead_code
		}
	}
	/**
	 * deactivate a public authentication or non repudiation key if activated as
	 * keys are always active, throw exception
	 */
	private void deactivateKey(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
	}
	/**
	 * internal authenticate generates a signature with the basic private key no
	 * security conditions needed if used for internal authentication only
	 * (Mutual authentication not supported)
	 */
	private void internalAuthenticate(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// check P1 and P2
		if ((buffer[ISO7816.OFFSET_P1] != ALG_SHA1_PKCS1) || buffer[ISO7816.OFFSET_P2] != BASIC)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		// receive the data that needs to be signed
		short byteRead = apdu.setIncomingAndReceive();
		// check Lc
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		// we do not support Lc=0x97, only Lc=0x16
		if ((lc == 0x97) || (byteRead == 0x97))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		if ((lc != 0x16) || (byteRead != 0x16))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		// the first data byte must be "94" and the second byte is the length
		// (20 bytes)
		if ((buffer[ISO7816.OFFSET_CDATA] != (byte) 0x94) || (buffer[ISO7816.OFFSET_CDATA + 1] != (byte) 0x14))
			ISOException.throwIt(ISO7816.SW_WRONG_DATA);
		// use the basic private key
		JCSystem.beginTransaction();
		////@ open valid(); // auto
		
		//@ transient_byte_arrays_mem(messageBuffer);
		//@ assert transient_byte_arrays(?as);
		//@ foreachp_remove(messageBuffer, as);
		//@ open transient_byte_array(messageBuffer);

		if (basicKeyPair == null)
			ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);

		//VF: bovenstaande is mogelijk bug in programma!
		cipher.init(basicKeyPair.getPrivate(), Cipher.MODE_ENCRYPT);
		// prepare the message buffer to the PKCS#1 (v1.5) structure
		preparePkcs1ClearText(messageBuffer, ALG_SHA1_PKCS1, lc);
		// copy the challenge (SHA1 hash) from the APDU to the message buffer
		Util.arrayCopy(buffer, (short) (ISO7816.OFFSET_CDATA + 2), messageBuffer, (short) 108, (short) 20);
		// generate signature
		cipher.doFinal(messageBuffer, (short) 0, (short) 128, buffer, (short) 0);
		// if T=0, store signature in sigBuffer so that it can latter be sent
		if (APDU.getProtocol() == APDU.PROTOCOL_T1) {
			Util.arrayCopy(buffer, (short) 0, responseBuffer, (short) 0, (short) 128);
			// in case T=1 protocol, send the signature immediately in a
			// response APDU
		} else {
			// send first 128 bytes (= 1024 bit) of buffer
			apdu.setOutgoingAndSend((short) 0, (short) 128);
		}
		// decrement internal authenticate counter
		//internalAuthenticateCounter--;
		//@ close transient_byte_array(messageBuffer);
		//@ foreachp_unremove(messageBuffer, as);
		
		////@ close valid(); // auto
		JCSystem.commitTransaction();
	}
	/**
	 * return the generated signature in a response APDU Used in T=0 protocol
	 */
	private void getResponse(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		////@ open [1/2]valid(); // auto
		// use P1 and P2 as offset
		short offset = Util.makeShort(buffer[ISO7816.OFFSET_P1], buffer[ISO7816.OFFSET_P2]);
		if (offset > responseBuffer.length)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		// inform the JCRE that the applet has data to return
		short le = apdu.setOutgoing();
		// if Le = 0, then return the complete signature (128 bytes = 1024 bits)
		// Le = 256 possible on real card
		if ((le == 0) || (le == 256))
			le = 128;
		// set the actual number of outgoing data bytes
		apdu.setOutgoingLength(le);
		// send content of sigBuffer in apdu
		if (offset + le > 128 || offset < 0)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		apdu.sendBytesLong(responseBuffer, offset, le);
		////@ close [1/2]valid(); // auto
	}
	/**
	 * generate a random challenge
	 */
	private void getChallenge(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// check P1 and P2
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00 || buffer[ISO7816.OFFSET_P2] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		// inform the JCRE that the applet has data to return
		short le = apdu.setOutgoing();
		// Le = 0 is not allowed
		if (le == 0)
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		JCSystem.beginTransaction();
		////@ open valid(); // auto
		RandomData random = EidCard.randomData;
		// generate random data and put it into buffer
		random.generateData(randomBuffer, (short) 0, le);
		// set the actual number of outgoing data bytes
		apdu.setOutgoingLength(le);
		// send content of buffer in apdu
		apdu.sendBytesLong(randomBuffer, (short) 0, le);
		////@ close valid(); // auto
		JCSystem.commitTransaction();
	}
	/**
	 * select a file on the eID card
	 * 
	 * this file can latter be read by a READ BINARY
	 */
	private void selectFile(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// check P2
		if (buffer[ISO7816.OFFSET_P2] != (byte) 0x0C)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		// P1 determines the select method
		switch (buffer[ISO7816.OFFSET_P1]) {
		case (byte) 0x02:
			selectByFileIdentifier(apdu, buffer);
			break;
		case (byte) 0x08:
			selectByPath(apdu, buffer);
			break;
		default:
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
			break; //~allow_dead_code
		}
	}
	/**
	 * set the previous APDU type to a certain value
	 */
	private void setPreviousApduType(byte type) 
  	    //@ requires previousApduType |-> ?thePreviousApduType &*& thePreviousApduType != null &*& thePreviousApduType.length == 1 &*& is_transient_byte_array(thePreviousApduType) == true &*& transient_byte_arrays(?ta) &*& foreachp(ta, transient_byte_array);
      	    //@ ensures previousApduType |-> thePreviousApduType &*& thePreviousApduType != null &*& transient_byte_arrays(ta) &*& foreachp(ta, transient_byte_array);
	{
		//@ transient_byte_arrays_mem(thePreviousApduType);
		//@ foreachp_remove(thePreviousApduType, ta);
		//@ open transient_byte_array(thePreviousApduType);
		previousApduType[0] = type;
		//@ close transient_byte_array(thePreviousApduType); // todo
		//@ foreachp_unremove(thePreviousApduType, ta);
	}
	/**
	 * return the previous APDU type
	 */
	private byte getPreviousApduType() 
  	    //@ requires [?f]previousApduType |-> ?thePreviousApduType &*& thePreviousApduType != null &*& thePreviousApduType.length == 1 &*& is_transient_byte_array(thePreviousApduType) == true &*& transient_byte_arrays(?ta) &*& foreachp(ta, transient_byte_array);
  	    //@ ensures [f]previousApduType |-> thePreviousApduType &*& transient_byte_arrays(ta) &*& foreachp(ta, transient_byte_array);
	{
		//@ transient_byte_arrays_mem(thePreviousApduType);
		//@ foreachp_remove(thePreviousApduType, ta);
		//@ open transient_byte_array(thePreviousApduType);
		return previousApduType[0];
		//@ close transient_byte_array(thePreviousApduType);
		//@ foreachp_unremove(thePreviousApduType, ta);
	}
	/**
	 * set the signature type to a certain value
	 */
	private void setSignatureType(byte type) 
  	    //@ requires signatureType |-> ?theSignatureType &*& theSignatureType != null &*& theSignatureType.length == 1 &*& is_transient_byte_array(theSignatureType) == true &*& transient_byte_arrays(?ta) &*& foreachp(ta, transient_byte_array);
      	    //@ ensures signatureType |-> theSignatureType &*& is_transient_byte_array(theSignatureType) == true &*& transient_byte_arrays(ta) &*& foreachp(ta, transient_byte_array);
	{
		//@ transient_byte_arrays_mem(theSignatureType);
		//@ foreachp_remove(theSignatureType, ta);
		//@ open transient_byte_array(theSignatureType);
		signatureType[0] = type;
		//@ close transient_byte_array(theSignatureType);
		//@ foreachp_unremove(theSignatureType, ta);
	}
	/**
	 * return the signature type
	 */
	private byte getSignatureType() 
  	    //@ requires [?f]signatureType |-> ?theSignatureType &*& theSignatureType != null &*& theSignatureType.length == 1 &*& is_transient_byte_array(theSignatureType) == true &*& transient_byte_arrays(?ta) &*& foreachp(ta, transient_byte_array);
      	    //@ ensures [f]signatureType |-> theSignatureType &*& transient_byte_arrays(ta) &*& foreachp(ta, transient_byte_array);
	{
		//@ transient_byte_arrays_mem(theSignatureType);
		//@ foreachp_remove(theSignatureType, ta);
		//@ open transient_byte_array(theSignatureType);
		return signatureType[0];
		//@ close transient_byte_array(theSignatureType);
		//@ foreachp_unremove(theSignatureType, ta);
	}
	

	/**
	 * deactivate a file on the eID card security conditions depend on file to
	 * activate: see belgian eID content file
	 */
	private void deactivateFile(APDU apdu, byte[] buffer) 
  	    //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
      	    //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
	{
		// check P2
		if (buffer[ISO7816.OFFSET_P2] != (byte) 0x0C)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		// P1 determines the select method
		switch (buffer[ISO7816.OFFSET_P1]) {
		case (byte) 0x02:
			selectByFileIdentifier(apdu, buffer);
			break;
		case (byte) 0x08:
			selectByPath(apdu, buffer);
			break;
		default:
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
			break; //~allow_dead_code
		}
		// check if deactivating this file is allowed
		if (!fileAccessAllowed(UPDATE_BINARY))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		JCSystem.beginTransaction();
		//@ open valid(); // todo
	  	//@ open selected_file_types(_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ?sf2);
		//@ sf2.castElementaryToFile();
		selectedFile.setActive(false);
		//@ sf2.castFileToElementary();
		////@ close valid(); // auto
		JCSystem.commitTransaction();
	}
}
