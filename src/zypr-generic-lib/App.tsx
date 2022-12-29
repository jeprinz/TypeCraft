import React from 'react'
import './App.css'
import { intToTestType } from '../TypeCraft/Purescript/output/TypeCraft.Purescript.InteropTest'
import { editor } from './zypr-generic/editor/EditorA1'
import { renderEditor } from './zypr-generic/Editor'

type Props = {}

type State = {}

export default class App extends React.Component<Props, State> {
  state = {}
  constructor(props: Props) {
    super(props)
  }

  render() {
    return (
      <div className="app">
        {editor}
      </div>
    )
  }
}
