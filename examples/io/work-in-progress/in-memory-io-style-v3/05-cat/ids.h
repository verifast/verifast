#ifndef IDS_H
#define IDS_H

/*                                                                    
 *        o---writer----------------------------------------------o             
 *       /                                                         \            
 * (splitA)                     o----cat_read---o                   \           
 *       \                     /                 \                   (joinA)    
 *        \          (cat_split)                  (cat_join)        /           
 *         \        /          \                 /         \       /            
 *          (splitB)            o----cat_write--o           (joinB)             
 *                  \                                      /                    
 *                   o---reader--------------------------o
 */

/*@

#define id_splitA(fam,sys)    id_init(fam,sys)
#define id_writer(fam,sys)    id_split_left(id_splitA(fam,sys))
#define id_splitB(fam,sys)    id_split_right(id_splitA(fam,sys))
#define id_cat_split(fam,sys) id_split_left(id_splitB(fam,sys))
#define id_cat_read(fam,sys)  id_split_left(id_cat_split(fam,sys))
#define id_cat_write(fam,sys) id_split_right(id_cat_split(fam,sys))
#define id_cat_join(fam,sys)  id_join(id_cat_read(fam,sys), id_cat_write(fam,sys))
#define id_reader(fam,sys)    id_split_right(id_splitB(fam,sys))
#define id_joinB(fam,sys)     id_join(id_cat_join(fam,sys), id_reader(fam,sys))
#define id_joinA(fam,sys)     id_join(id_writer(fam,sys), id_joinB(fam,sys))
@*/

#endif
