#ifndef IDS_H
#define IDS_H

/*                                                                    
 *        o---writer----------------------------------------------o             
 *                                                                              
 *                              o----cat_read---o                               
 *                             /                 \                              
 *                   (cat_split)                  (cat_join)                    
 *                             \                 /                              
 *                              o----cat_write--o                               
 *                                                                              
 *                   o---reader--------------------------o
 */

/*@


#define id_writer(fam)    id_init(fam)

#define id_cat_split(fam) id_init(fam)
#define id_cat_read(fam)  id_split_left(id_cat_split(fam))
#define id_cat_write(fam) id_split_right(id_cat_split(fam))
#define id_cat_join(fam)  id_join(id_cat_read(fam), id_cat_write(fam))

#define id_reader(fam)    id_init(fam)
@*/

#endif
