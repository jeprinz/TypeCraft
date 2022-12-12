import React from 'react'
import './App.css'
// import './zypr-generic/frontend/Frontend1.css'
// import editor from "./zypr-generic/editor/EditorAlphaA1"
// import './zypr-generic/frontend/Frontend2.css'
// import editor from './zypr-generic/editor/EditorBetaB2'
import './zypr-generic/frontend/Frontend3.css'
import editor from './zypr-generic/editor/EditorGammaC3'
import { intToTestType } from '../TypeCraft/Purescript/output/TypeCraft.Purescript.InteropTest'

type Props = {}

type State = {}

export default class App extends React.Component<Props, State> {
  state = {}
  constructor(props: Props) {
    super(props)
  }

  render() {
    console.log(intToTestType(100))

    // const Editor = this.state.editor
    return (
      <div className="app">
        {editor()}
      </div>
    )
  }
}
