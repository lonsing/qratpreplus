#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <libgen.h>
#include <unistd.h>
#include <sys/wait.h>
#include "../qratpreplus.h"

int
main (int argc, char **argv)
{
  if (argc < 2)
    {
      fprintf (stderr, "Error: expecting input filename as first argument!\n");
      exit (1);
    }

  fprintf (stderr, "Creating QRATPre+ object.\n");
  QRATPrePlus *qr = qratpreplus_create ();

  fprintf (stderr, "Creating second QRATPre+ object\n");
  QRATPrePlus *other = qratpreplus_create ();

  /* Pass command line args to both application objects. */
  int i;
  for (i = 2; i < argc; i++)
    {
      char * configstr = argv[i];
      qratpreplus_configure (qr, configstr);
      qratpreplus_configure (other, configstr);
    }
  
  /* Import formula from file. */
  char *inputfilename = argv[1];
  fprintf (stderr, "Input filename: %s\n", inputfilename);
  qratpreplus_add_formula (qr, inputfilename);

  /* Add formula from 'qr' to 'other', using API functions. */

  /* Declare the maximum variable ID appearing in the formula. */
  qratpreplus_declare_max_var_id (other, qratpreplus_get_max_var_id (qr));

  int *tmp_buffer = 0;

  /* Export quantifier prefix via iterator API. */
  qratpreplus_qbl_iter_init (qr);
  while (qratpreplus_qbl_iter_has_next (qr))
    {
      /* Get number of variables in qblock to be exported next and
         allocate space in 'tmp_buffer'. */
      int len = qratpreplus_qbl_iter_next_len (qr);
      assert (len >= 0);
      /* Must allocate space for at least one item, even if 'len == 0'. */
      tmp_buffer = realloc (tmp_buffer, (len == 0 ? len + 1 : len) * sizeof (int));
      /* Get array of variables, will be copied to 'tmp_buffer'. */
      tmp_buffer = qratpreplus_qbl_iter_get_vars (qr, tmp_buffer);
      assert (tmp_buffer);
      /* Get qblock type and advance iterator. */
      int qtype = qratpreplus_qbl_iter_next (qr);
      assert (qtype != 0);
      /* Create new qblock in 'other' and import variables. */
      qratpreplus_new_qblock (other, qtype);
      int *p, *e;
      for (p = tmp_buffer, e = p + len; p < e; p++)
        qratpreplus_add_var_to_qblock (other, *p);
      qratpreplus_add_var_to_qblock (other, 0);
      assert (tmp_buffer);
    }
    
  /* Export clauses via iterator API. */
  qratpreplus_cl_iter_init (qr);
  while (qratpreplus_cl_iter_has_next (qr))
    {
      /* Get number of literals to be exported. */
      int len = qratpreplus_cl_iter_next_len (qr);
      assert (len >= 0);
      /* Must allocate space for at least one item, even if 'len == 0'. */
      tmp_buffer = realloc (tmp_buffer, (len == 0 ? len + 1 : len) * sizeof (int));
      /* Get array of literals, will be copied to 'tmp_buffer',
         advance iterator. */
      tmp_buffer = qratpreplus_cl_iter_next (qr, tmp_buffer);
      assert (tmp_buffer);
      /* Import literals. */
      int *p, *e;
      for (p = tmp_buffer, e = p + len; p < e; p++)
        qratpreplus_add_literal (other, *p);
      qratpreplus_add_literal (other, 0);
      assert (tmp_buffer);
    }

  /* Preprocess the formula in 'other'. The default configuration is
     used unless another configuration was set via arguments and the
     'configure'-function of the API. */
  qratpreplus_preprocess (other);
  
  fprintf (stderr, "Printing preprocessed formula of other object.\n");
  qratpreplus_print_formula (other, stdout);
  
  fprintf (stderr, "Deleting QRATPre+ objects.\n");
  qratpreplus_delete (qr);
  qratpreplus_delete (other);
  free (tmp_buffer);
  return 0;
}
