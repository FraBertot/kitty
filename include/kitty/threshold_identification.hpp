/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "operations.hpp"
#include "isop.hpp"
#include "cube.hpp"
#include "dynamic_truth_table.hpp"
#include "static_truth_table.hpp"

namespace kitty
{

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;

  /* TODO */

  auto Nvar = tt.num_vars();
  auto flip_tt = tt;
  std::vector<bool> flip_flag;

  // check for tt to be unate or binate & convert it into a positive unate
  for (auto i = 0u; i < Nvar; ++i)
  {
    auto pos_cof = cofactor1( tt, i);
    auto neg_cof = cofactor0( tt, i);

    if (implies(neg_cof, pos_cof)) //positive unate in variable i
    {
      flip_flag.emplace_back(false); //no flip has occurred for variable i
    }
    else if(implies(pos_cof, neg_cof)) //negarive unate in variable i
    {
      flip_tt = flip( flip_tt, i );
      flip_flag.emplace_back(true); //flip for variable i
    }
    else
    {
      return false;
    }
  }

  lprec* lp;
  int *num_col = nullptr, j;
  bool flag = false;
  REAL* weights = nullptr;

  /* We will build the model row by row */
  int Ncol = Nvar + 1;
  auto T = Ncol;
  lp = make_lp( 0, Ncol );
  if ( lp == nullptr )
    flag = true; /* couldn't construct a new model... */

  if ( !flag )
  {
    /* create space large enough for one row */
    num_col = (int*)malloc( Ncol * sizeof( *num_col ) );
    weights = (REAL*)malloc( Ncol * sizeof( *weights ) );
    if ( ( num_col == nullptr ) || ( weights == nullptr ) )
      flag = true;
  }

  set_add_rowmode( lp, TRUE );
  if (!flag)
  {
    std::vector<cube> tt_on_set = isop( flip_tt ); //get the onset of the tt
    for ( cube cb : tt_on_set ) // Constraints for on_set
    {
      j = 0;
      for ( int i = 0; i < Ncol - 1; ++i )
      {
        num_col[j] = i + 1;
        if ( cb.get_mask( i ) ) // if variable is in cube
          weights[j] = 1;
        else
          weights[j] = 0;
        ++j;
      }
      num_col[j] = T;
      weights[j] = - 1;
      if ( !add_constraintex( lp, j + 1, weights, num_col, GE, 0 ) )
        flag = true;
    }
  }

  if (!flag)
  {
    std::vector<cube> tt_off_set = isop( unary_not( flip_tt ) );  //get the offset of tt
    for ( cube cb : tt_off_set )  // Constrains for off_set
    {
      j = 0;
      for ( int i = 0; i < Ncol - 1; ++i )
      {
        num_col[j] = i + 1;
        if ( !cb.get_mask( i ) ) //if the variable is not in cube
          weights[j] = 1;
        else
          weights[j] = 0;
        ++j;
      }
      num_col[j] = T;
      weights[j] = - 1;
      if ( !add_constraintex( lp, j + 1, weights, num_col, LE, - 1 ) )
        flag = true;
    }
  }

  /* set the objective function : min(sum(w_i) + T) */
  if (!flag)
  {
    //num_col[Ncol - 1] = T;
    for ( int f = 0; f < Ncol; ++f )
    {
      num_col[f] = f + 1;
      weights[f] = 1;
    }
    /* set the objective in lpsolve */
    if ( !set_obj_fnex( lp, Ncol, weights, num_col ) )
      flag = true;
  }

  if (!flag)
  {
    for ( int m = 0; m < Ncol; ++m )  //Last condition: all weights and T must be positive
    {
      for ( int n = 0; n < Ncol; ++n )
      {
        if ( m == n )
        {
          num_col[m] = m + 1;
          weights[m] = 1;
        }
        else
        {
          num_col[n] = n + 1;
          weights[n] = 0;
        }
      }
      if ( !add_constraintex( lp, Ncol, weights, num_col, GE, 0 ) )
        flag = false;
    }
  }

  set_add_rowmode( lp, FALSE );

  /* set the object direction to minimize */
  set_minim( lp );
  set_verbose( lp, IMPORTANT );
  if ( solve( lp ) != OPTIMAL ) //Not a TF if LP doesn't give an optimal solution
    return false;

  /* push the weight and threshold values into `linear_form` */
  get_variables(lp, weights);
  auto T_update = weights[Ncol-1];
  for ( j = 0; j < Ncol -1; ++j)
  {
    if (!flip_flag[j])  //variable p not flipped
      linear_form.emplace_back( weights[j] );
    else  //variable p flipped
    {
      linear_form.emplace_back( -weights[j] );
      T_update = T_update - weights[j];  //updating the threshold
    }
  }
  linear_form.emplace_back( T_update );
  if ( plf )
  {
    *plf = linear_form;
  }

  /* free allocated memory */
  if ( weights != nullptr )
    free( weights );
  if ( num_col != nullptr )
    free( num_col );
  if ( lp != nullptr )
  {
    /* clean up such that all used memory by lpsolve is freed */
    delete_lp( lp );
  }

  return true;
}

} /* namespace kitty */
